//! Токенизатор арифметических выражений.
//!
//! # Пример
//!
//! ```
//! use calculator_rs::token::{Tokenizer, Token};
//!
//! let tokens: Vec<Token> = Tokenizer::new("(1 + 2)")
//!     .map(|r| r.map(|st| st.token))
//!     .collect::<Result<_, _>>()
//!     .unwrap();
//! ```

use std::{fmt::Display, num::ParseIntError};
use thiserror::Error;

/// Токен арифметического выражения.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Token {
    /// Беззнаковое целое число (знак обрабатывается как унарный оператор).
    Number(u64),
    /// Оператор: `+`, `-`, `*`, `/`.
    Symbol(char),
    /// Открывающая скобка `(`.
    OpenBracket,
    /// Закрывающая скобка `)`.
    CloseBracket,
}

/// Токен с информацией о позиции в исходной строке.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct SpannedToken {
    /// Сам токен.
    pub token: Token,
    /// Позиция начала токена (в байтах от начала строки).
    pub pos: usize,
}

impl SpannedToken {
    /// Создаёт новый токен с позицией.
    pub const fn new(token: Token, pos: usize) -> Self {
        Self { token, pos }
    }
}

/// Ошибка токенизации.
#[derive(Error, Debug, PartialEq, Eq, Clone)]
#[error("позиция {pos}: {kind}")]
pub struct TokenError {
    /// Позиция ошибки в исходной строке.
    pub pos: usize,
    /// Тип ошибки.
    pub kind: TokenErrorKind,
}

impl TokenError {
    const fn new(pos: usize, kind: TokenErrorKind) -> Self {
        Self { pos, kind }
    }
}

/// Тип ошибки токенизации.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TokenErrorKind {
    /// Неизвестный символ.
    UnknownSymbol(char),
    /// Ошибка разбора числа.
    NumberError(ParseIntError),
}

impl Display for TokenErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnknownSymbol(symbol) => write!(f, "неизвестный символ '{symbol}'"),
            Self::NumberError(err) => write!(f, "ошибка разбора числа: {err}"),
        }
    }
}

/// Итератор по токенам входной строки.
pub struct Tokenizer<'a> {
    input: &'a str,
    pos: usize,
}

impl<'a> Tokenizer<'a> {
    /// Создаёт новый токенизатор для входной строки.
    pub const fn new(input: &'a str) -> Self {
        Self { input, pos: 0 }
    }

    fn peek(&self) -> Option<char> {
        self.input.chars().next()
    }

    fn advance(&mut self) -> Option<char> {
        let mut chars = self.input.chars();
        let ch = chars.next()?;
        self.input = chars.as_str();
        self.pos += ch.len_utf8();
        Some(ch)
    }

    fn advance_while(&mut self, predicate: impl Fn(char) -> bool) -> &'a str {
        let byte_len: usize = self
            .input
            .chars()
            .take_while(|&c| predicate(c))
            .map(char::len_utf8)
            .sum();

        let (consumed, rest) = self.input.split_at(byte_len);
        self.pos += byte_len;
        self.input = rest;
        consumed
    }

    fn skip_whitespace(&mut self) {
        self.advance_while(char::is_whitespace);
    }

    fn read_number(&mut self, start_pos: usize) -> Result<SpannedToken, TokenError> {
        let num_str = self.advance_while(|c| c.is_ascii_digit());

        num_str
            .parse()
            .map(|n| SpannedToken::new(Token::Number(n), start_pos))
            .map_err(|err| TokenError::new(start_pos, TokenErrorKind::NumberError(err)))
    }
}

impl Iterator for Tokenizer<'_> {
    type Item = Result<SpannedToken, TokenError>;

    fn next(&mut self) -> Option<Self::Item> {
        self.skip_whitespace();

        let start_pos = self.pos;
        let ch = self.peek()?;

        let token = match ch {
            '(' | ')' => {
                self.advance();
                let token = if ch == '(' {
                    Token::OpenBracket
                } else {
                    Token::CloseBracket
                };
                Ok(SpannedToken::new(token, start_pos))
            }
            '+' | '-' | '*' | '/' => {
                self.advance();
                Ok(SpannedToken::new(Token::Symbol(ch), start_pos))
            }
            '0'..='9' => self.read_number(start_pos),
            _ => {
                self.advance();
                Err(TokenError::new(
                    start_pos,
                    TokenErrorKind::UnknownSymbol(ch),
                ))
            }
        };

        Some(token)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tokenize(input: &str) -> Result<Vec<Token>, TokenError> {
        Tokenizer::new(input)
            .map(|r| r.map(|st| st.token))
            .collect()
    }

    #[test]
    fn tokenize_numbers() {
        assert_eq!(tokenize("42").unwrap(), vec![Token::Number(42)]);
        assert_eq!(tokenize("0").unwrap(), vec![Token::Number(0)]);
        assert_eq!(
            tokenize("123 456").unwrap(),
            vec![Token::Number(123), Token::Number(456)]
        );
    }

    #[test]
    fn tokenize_operators() {
        assert_eq!(
            tokenize("+ - * /").unwrap(),
            vec![
                Token::Symbol('+'),
                Token::Symbol('-'),
                Token::Symbol('*'),
                Token::Symbol('/'),
            ]
        );
    }

    #[test]
    fn tokenize_brackets() {
        assert_eq!(
            tokenize("()").unwrap(),
            vec![Token::OpenBracket, Token::CloseBracket]
        );
    }

    #[test]
    fn tokenize_expression() {
        assert_eq!(
            tokenize("(1 + 2)").unwrap(),
            vec![
                Token::OpenBracket,
                Token::Number(1),
                Token::Symbol('+'),
                Token::Number(2),
                Token::CloseBracket,
            ]
        );
    }

    #[test]
    fn tokenize_large_number() {
        // u64::MAX
        let input = "18446744073709551615";
        assert_eq!(
            tokenize(input).unwrap(),
            vec![Token::Number(18446744073709551615)]
        );
    }

    #[test]
    fn tokenize_unknown_symbol() {
        let result = tokenize("1 @ 2");
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert_eq!(err.pos, 2);
        assert!(matches!(err.kind, TokenErrorKind::UnknownSymbol('@')));
    }

    #[test]
    fn spanned_tokens_have_correct_positions() {
        let tokens: Vec<_> = Tokenizer::new("1 + 23").collect::<Result<_, _>>().unwrap();

        assert_eq!(tokens[0].pos, 0); // '1' at position 0
        assert_eq!(tokens[1].pos, 2); // '+' at position 2
        assert_eq!(tokens[2].pos, 4); // '23' at position 4
    }
}

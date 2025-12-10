//! Модуль токенизации арифметических выражений.
//!
//! Поддерживает:
//! - Целые числа (i64)
//! - Операторы: `+`, `-`, `*`, `/`
//! - Скобки: `(`, `)`
//!
//! # Пример
//!
//! ```
//! use calculator_rs::token::{Tokenizer, Token};
//!
//! let tokens: Vec<Token> = Tokenizer::new("(1 + 2)")
//!     .collect::<Result<_, _>>()
//!     .unwrap();
//!
//! assert_eq!(tokens, vec![
//!     Token::OpenBracket,
//!     Token::Number(1),
//!     Token::Symbol('+'),
//!     Token::Number(2),
//!     Token::CloseBracket,
//! ]);
//! ```

use std::{fmt::Display, num::ParseIntError};
use thiserror::Error;

/// Токен арифметического выражения.
///
/// # Примеры
///
/// ```
/// use calculator_rs::token::Token;
///
/// let num = Token::Number(42);
/// let op = Token::Symbol('+');
/// let open = Token::OpenBracket;
/// let close = Token::CloseBracket;
///
/// assert_eq!(num, Token::Number(42));
/// ```
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Token {
    /// Целое число.
    Number(i64),
    /// Оператор (`+`, `-`, `*`, `/`).
    Symbol(char),
    /// Открывающая скобка `(`.
    OpenBracket,
    /// Закрывающая скобка `)`.
    CloseBracket,
}

/// Ошибка токенизации с позицией в исходной строке.
///
/// # Примеры
///
/// ```
/// use calculator_rs::token::{Tokenizer, TokenErrorKind};
///
/// let mut tokenizer = Tokenizer::new("  @");
/// let err = tokenizer.next().unwrap().unwrap_err();
///
/// assert_eq!(err.pos, 2);
/// assert_eq!(err.kind, TokenErrorKind::UnknownSymbol('@'));
/// assert_eq!(err.to_string(), "TokenError at position 2: unknown symbol '@'");
/// ```
#[derive(Error, Debug, PartialEq, Eq)]
#[error("TokenError at position {pos}: {kind}")]
pub struct TokenError {
    /// Позиция ошибки (byte offset от начала строки).
    pub pos: usize,
    /// Тип ошибки.
    pub kind: TokenErrorKind,
}

impl TokenError {
    /// Создаёт новую ошибку токенизации.
    const fn new(pos: usize, kind: TokenErrorKind) -> Self {
        Self { pos, kind }
    }
}

/// Тип ошибки токенизации.
///
/// # Display
///
/// ```
/// use calculator_rs::token::TokenErrorKind;
///
/// let unknown = TokenErrorKind::UnknownSymbol('?');
/// assert_eq!(unknown.to_string(), "unknown symbol '?'");
/// ```
#[derive(Debug, PartialEq, Eq)]
pub enum TokenErrorKind {
    /// Неизвестный символ.
    UnknownSymbol(char),
    /// Ошибка парсинга числа (например, переполнение).
    NumberError(ParseIntError),
}

impl Display for TokenErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnknownSymbol(symbol) => write!(f, "unknown symbol '{symbol}'"),
            Self::NumberError(err) => write!(f, "number parse error: {err}"),
        }
    }
}

/// Токенизатор арифметических выражений.
///
/// Реализует [`Iterator`], позволяя итерироваться по токенам.
///
/// # Примеры
///
/// Базовое использование:
///
/// ```
/// use calculator_rs::token::{Tokenizer, Token};
///
/// let mut tokenizer = Tokenizer::new("42 + 8");
///
/// assert_eq!(tokenizer.next(), Some(Ok(Token::Number(42))));
/// assert_eq!(tokenizer.next(), Some(Ok(Token::Symbol('+'))));
/// assert_eq!(tokenizer.next(), Some(Ok(Token::Number(8))));
/// assert_eq!(tokenizer.next(), None);
/// ```
///
/// Сбор всех токенов:
///
/// ```
/// use calculator_rs::token::{Tokenizer, Token};
///
/// let tokens: Result<Vec<_>, _> = Tokenizer::new("1 + 2").collect();
/// assert!(tokens.is_ok());
/// ```
///
/// Обработка ошибок:
///
/// ```
/// use calculator_rs::token::{Tokenizer, TokenErrorKind};
///
/// let result: Result<Vec<_>, _> = Tokenizer::new("1 + @").collect();
/// let err = result.unwrap_err();
///
/// assert_eq!(err.pos, 4);
/// assert_eq!(err.kind, TokenErrorKind::UnknownSymbol('@'));
/// ```
pub struct Tokenizer<'a> {
    input: &'a str,
    pos: usize,
}

impl<'a> Tokenizer<'a> {
    /// Создаёт новый токенизатор для заданной строки.
    ///
    /// # Примеры
    ///
    /// ```
    /// use calculator_rs::token::Tokenizer;
    ///
    /// let tokenizer = Tokenizer::new("1 + 2");
    /// assert_eq!(tokenizer.count(), 3);
    /// ```
    pub const fn new(input: &'a str) -> Self {
        Self { input, pos: 0 }
    }

    /// Возвращает следующий символ без продвижения позиции.
    fn peek(&self) -> Option<char> {
        self.input.chars().next()
    }

    /// Продвигает позицию на один символ и возвращает его.
    fn advance(&mut self) -> Option<char> {
        let mut chars = self.input.chars();
        let ch = chars.next()?;
        self.input = chars.as_str();
        self.pos += ch.len_utf8();
        Some(ch)
    }

    /// Продвигает позицию пока предикат возвращает `true`.
    /// Возвращает срез прочитанных символов.
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

    /// Пропускает пробельные символы.
    fn skip_whitespace(&mut self) {
        self.advance_while(char::is_whitespace);
    }

    /// Читает число и возвращает токен или ошибку.
    fn read_number(&mut self) -> Result<Token, TokenError> {
        let start_pos = self.pos;
        let num_str = self.advance_while(|c| c.is_ascii_digit());

        num_str
            .parse()
            .map(Token::Number)
            .map_err(|err| TokenError::new(start_pos, TokenErrorKind::NumberError(err)))
    }
}

impl Iterator for Tokenizer<'_> {
    type Item = Result<Token, TokenError>;

    fn next(&mut self) -> Option<Self::Item> {
        self.skip_whitespace();

        let ch = self.peek()?;

        let token = match ch {
            '(' | ')' => {
                self.advance();
                Ok(if ch == '(' {
                    Token::OpenBracket
                } else {
                    Token::CloseBracket
                })
            }
            '+' | '-' | '*' | '/' => {
                self.advance();
                Ok(Token::Symbol(ch))
            }
            '0'..='9' => self.read_number(),
            _ => {
                let pos = self.pos;
                self.advance();
                Err(TokenError::new(pos, TokenErrorKind::UnknownSymbol(ch)))
            }
        };

        Some(token)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tokenize(input: &str) -> Vec<Token> {
        Tokenizer::new(input)
            .collect::<Result<Vec<_>, _>>()
            .expect("Tokenization failed")
    }

    #[test]
    fn test_single_tokens() {
        let cases = [
            ("+", Token::Symbol('+')),
            ("-", Token::Symbol('-')),
            ("*", Token::Symbol('*')),
            ("/", Token::Symbol('/')),
            ("(", Token::OpenBracket),
            (")", Token::CloseBracket),
            ("42", Token::Number(42)),
        ];

        for (input, expected) in cases {
            assert_eq!(tokenize(input), vec![expected], "Failed for input: {input}");
        }
    }

    #[test]
    fn test_expression() {
        assert_eq!(
            tokenize("(1 + 2)"),
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
    fn test_nested_expression() {
        assert_eq!(
            tokenize("(1 - (2 + 3))"),
            vec![
                Token::OpenBracket,
                Token::Number(1),
                Token::Symbol('-'),
                Token::OpenBracket,
                Token::Number(2),
                Token::Symbol('+'),
                Token::Number(3),
                Token::CloseBracket,
                Token::CloseBracket,
            ]
        );
    }

    #[test]
    fn test_unknown_symbol() {
        let err = Tokenizer::new("  ?").next().unwrap().unwrap_err();

        assert_eq!(err.pos, 2);
        assert_eq!(err.kind, TokenErrorKind::UnknownSymbol('?'));
    }

    #[test]
    fn test_number_overflow() {
        let err = Tokenizer::new(&"9".repeat(100))
            .next()
            .unwrap()
            .unwrap_err();

        assert_eq!(err.pos, 0);
        assert!(matches!(err.kind, TokenErrorKind::NumberError(_)));
    }

    #[test]
    fn test_whitespace_handling() {
        assert_eq!(
            tokenize("  1   +   2  "),
            vec![Token::Number(1), Token::Symbol('+'), Token::Number(2)]
        );
    }

    #[test]
    fn test_empty_input() {
        assert!(tokenize("").is_empty());
        assert!(tokenize("   ").is_empty());
    }

    mod error_messages {
        use super::*;

        #[test]
        fn test_unknown_symbol_display() {
            let kind = TokenErrorKind::UnknownSymbol('?');
            assert_eq!(kind.to_string(), "unknown symbol '?'");

            let kind = TokenErrorKind::UnknownSymbol('@');
            assert_eq!(kind.to_string(), "unknown symbol '@'");

            let kind = TokenErrorKind::UnknownSymbol('日');
            assert_eq!(kind.to_string(), "unknown symbol '日'");
        }

        #[test]
        fn test_number_error_matches_parse_error() {
            let big_number = "9".repeat(100);

            // Получаем ошибку из токенизатора
            let token_err = Tokenizer::new(&big_number).next().unwrap().unwrap_err();

            // Получаем ошибку напрямую из parse
            let parse_err = big_number.parse::<i64>().unwrap_err();

            // Сравниваем
            assert_eq!(token_err.pos, 0);
            assert_eq!(token_err.kind, TokenErrorKind::NumberError(parse_err));
        }

        #[test]
        fn test_number_error_display_matches_parse() {
            let big_number = "9".repeat(100);

            let token_err = Tokenizer::new(&big_number).next().unwrap().unwrap_err();

            let parse_err = big_number.parse::<i64>().unwrap_err();

            // Display тоже должен совпадать
            assert_eq!(
                token_err.kind.to_string(),
                format!("number parse error: {parse_err}")
            );
        }

        #[test]
        fn test_token_error_full_display() {
            let err = TokenError::new(5, TokenErrorKind::UnknownSymbol('#'));
            assert_eq!(
                err.to_string(),
                "TokenError at position 5: unknown symbol '#'"
            );

            // Для NumberError
            let big_number = "9".repeat(100);
            let parse_err = big_number.parse::<i64>().unwrap_err();
            let err = TokenError::new(0, TokenErrorKind::NumberError(parse_err.clone()));

            assert_eq!(
                err.to_string(),
                format!("TokenError at position 0: number parse error: {parse_err}")
            );
        }
    }

    mod unicode {
        use super::*;

        #[test]
        fn test_unicode_whitespace() {
            // Em space (U+2003)
            assert_eq!(tokenize("1\u{2003}+\u{2003}2"), tokenize("1 + 2"));
        }

        #[test]
        fn test_unicode_unknown_symbol_position() {
            // "1 + 日" — символ 日 на позиции 4 (после "1 + ")
            let err = Tokenizer::new("1 + 日").last().unwrap().unwrap_err();
            assert_eq!(err.pos, 4);
            assert_eq!(err.kind, TokenErrorKind::UnknownSymbol('日'));
        }
    }
}

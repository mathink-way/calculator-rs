//! Рекурсивный нисходящий парсер арифметических выражений.
//!
//! Преобразует поток [`Token`] в дерево выражений ([`Expr`]).
//!
//! # Грамматика
//!
//! ```text
//! expr   = term (('+' | '-') term)*
//! term   = unary (('*' | '/') unary)*
//! unary  = ('+' | '-')? factor
//! factor = NUMBER | '(' expr ')'
//! ```
//!
//! Приоритет (от высшего к низшему):
//! 1. Скобки `()`
//! 2. Унарные `+`, `-`
//! 3. Умножение `*`, деление `/`
//! 4. Сложение `+`, вычитание `-`
//!
//! Все бинарные операторы левоассоциативны.
//!
//! # Примеры
//!
//! ```
//! use calculator_rs::parser::parse;
//!
//! let expr = parse("2 + 3 * 4").unwrap();
//! assert_eq!(expr.evaluate().unwrap(), 14);
//!
//! // Поддержка i64::MIN
//! let expr = parse("-9223372036854775808").unwrap();
//! assert_eq!(expr.evaluate().unwrap(), i64::MIN);
//! ```

use std::iter::Peekable;

use thiserror::Error;

use crate::expression::{BinaryOp, Expr, UnaryOp};
use crate::token::{SpannedToken, Token, TokenError, Tokenizer};

/// Ошибки, возникающие при разборе выражения.
#[derive(Error, Debug, PartialEq, Eq)]
pub enum ParseError {
    /// Неожиданный конец ввода.
    #[error("неожиданный конец ввода")]
    UnexpectedEof,

    /// Встречен неожиданный токен.
    #[error("неожиданный токен: {token:?}")]
    UnexpectedToken {
        /// Неожиданный токен.
        token: Token,
        /// Позиция токена.
        pos: usize,
    },

    /// Ошибка, переданная от токенизатора.
    #[error("{0}")]
    TokenError(#[from] TokenError),

    /// Отсутствует закрывающая скобка.
    #[error("отсутствует закрывающая скобка")]
    UnclosedParen {
        /// Позиция открывающей скобки.
        open_pos: usize,
    },

    /// Число вне допустимого диапазона i64.
    #[error("число вне диапазона i64")]
    NumberOutOfRange {
        /// Позиция числа.
        pos: usize,
    },
}

impl ParseError {
    /// Возвращает позицию ошибки, если она известна.
    #[must_use]
    pub const fn position(&self) -> Option<usize> {
        match self {
            Self::UnexpectedEof => None,
            Self::UnexpectedToken { pos, .. } => Some(*pos),
            Self::TokenError(te) => Some(te.pos),
            Self::UnclosedParen { open_pos } => Some(*open_pos),
            Self::NumberOutOfRange { pos } => Some(*pos),
        }
    }
}

/// Рекурсивный нисходящий парсер арифметических выражений.
pub struct Parser<'a> {
    tokens: Peekable<Tokenizer<'a>>,
}

impl<'a> Parser<'a> {
    /// Создаёт новый парсер для заданной входной строки.
    #[must_use]
    pub fn new(input: &'a str) -> Self {
        Self {
            tokens: Tokenizer::new(input).peekable(),
        }
    }

    /// Разбирает ввод и возвращает дерево выражения.
    ///
    /// # Ошибки
    ///
    /// Возвращает [`ParseError`] при синтаксических ошибках.
    pub fn parse(mut self) -> Result<Expr, ParseError> {
        let expr = self.expr()?;

        match self.tokens.next() {
            None => Ok(expr),
            Some(Ok(st)) => Err(ParseError::UnexpectedToken {
                token: st.token,
                pos: st.pos,
            }),
            Some(Err(err)) => Err(err.into()),
        }
    }

    fn peek(&mut self) -> Option<&Result<SpannedToken, TokenError>> {
        self.tokens.peek()
    }

    fn advance(&mut self) -> Option<Result<SpannedToken, TokenError>> {
        self.tokens.next()
    }

    /// Пытается сопоставить один из заданных символов.
    /// Возвращает (символ, позиция) при успехе.
    fn match_symbol(&mut self, expected: &[char]) -> Option<(char, usize)> {
        let (matched, pos) = match self.peek()? {
            Ok(SpannedToken {
                token: Token::Symbol(c),
                pos,
            }) if expected.contains(c) => (*c, *pos),
            _ => return None,
        };
        self.advance();
        Some((matched, pos))
    }

    /// Разбирает: `expr = term (('+' | '-') term)*`
    fn expr(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.term()?;

        while let Some((op, _)) = self.match_symbol(&['+', '-']) {
            let right = self.term()?;
            let kind = match op {
                '+' => BinaryOp::Add,
                '-' => BinaryOp::Sub,
                _ => unreachable!(),
            };
            left = Expr::binary(kind, left, right);
        }

        Ok(left)
    }

    /// Разбирает: `term = unary (('*' | '/') unary)*`
    fn term(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.unary()?;

        while let Some((op, _)) = self.match_symbol(&['*', '/']) {
            let right = self.unary()?;
            let kind = match op {
                '*' => BinaryOp::Mul,
                '/' => BinaryOp::Div,
                _ => unreachable!(),
            };
            left = Expr::binary(kind, left, right);
        }

        Ok(left)
    }

    /// Разбирает: `unary = ('+' | '-')? factor`
    fn unary(&mut self) -> Result<Expr, ParseError> {
        if let Some((op, _)) = self.match_symbol(&['+', '-']) {
            // Специальная обработка: унарный минус перед числом
            // Это нужно для поддержки i64::MIN (-9223372036854775808)
            if op == '-' {
                if let Some(Ok(SpannedToken {
                    token: Token::Number(n),
                    pos,
                })) = self.peek()
                {
                    let n = *n;
                    let pos = *pos;
                    self.advance();
                    return Self::make_negative_literal(n, pos);
                }
            }

            let child = self.unary()?;
            let kind = match op {
                '+' => UnaryOp::Plus,
                '-' => UnaryOp::Neg,
                _ => unreachable!(),
            };
            return Ok(Expr::unary(kind, child));
        }

        self.factor()
    }

    /// Создаёт отрицательный литерал из беззнакового числа.
    fn make_negative_literal(n: u64, pos: usize) -> Result<Expr, ParseError> {
        const I64_MIN_ABS: u64 = i64::MAX as u64 + 1; // 9223372036854775808

        if n <= i64::MAX as u64 {
            // Безопасное отрицание
            Ok(Expr::literal(-(n as i64)))
        } else if n == I64_MIN_ABS {
            // Особый случай: i64::MIN
            Ok(Expr::literal(i64::MIN))
        } else {
            Err(ParseError::NumberOutOfRange { pos })
        }
    }

    /// Разбирает: `factor = NUMBER | '(' expr ')'`
    fn factor(&mut self) -> Result<Expr, ParseError> {
        let spanned = self.advance().ok_or(ParseError::UnexpectedEof)??;

        match spanned.token {
            Token::Number(n) => {
                if n <= i64::MAX as u64 {
                    Ok(Expr::literal(n as i64))
                } else {
                    Err(ParseError::NumberOutOfRange { pos: spanned.pos })
                }
            }
            Token::OpenBracket => {
                let open_pos = spanned.pos;
                let inner = self.expr()?;
                match self.advance() {
                    Some(Ok(SpannedToken {
                        token: Token::CloseBracket,
                        ..
                    })) => Ok(inner),
                    Some(Ok(st)) => Err(ParseError::UnexpectedToken {
                        token: st.token,
                        pos: st.pos,
                    }),
                    Some(Err(e)) => Err(e.into()),
                    None => Err(ParseError::UnclosedParen { open_pos }),
                }
            }
            token => Err(ParseError::UnexpectedToken {
                token,
                pos: spanned.pos,
            }),
        }
    }
}

/// Разбирает строку в дерево выражения.
///
/// # Ошибки
///
/// Возвращает [`ParseError`] при некорректном синтаксисе.
///
/// # Примеры
///
/// ```
/// use calculator_rs::parser::parse;
///
/// assert_eq!(parse("2 + 2").unwrap().evaluate().unwrap(), 4);
/// assert_eq!(parse("-9223372036854775808").unwrap().evaluate().unwrap(), i64::MIN);
/// ```
pub fn parse(input: &str) -> Result<Expr, ParseError> {
    Parser::new(input).parse()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expression::EvalError;

    // ─────────────────────────────────────────────────────────────────────────
    // Параметризованные тесты вычислений
    // ─────────────────────────────────────────────────────────────────────────

    macro_rules! eval_tests {
        ($($name:ident: $input:expr => $expected:expr),* $(,)?) => {
            $(
                #[test]
                fn $name() {
                    let expr = parse($input).unwrap_or_else(|e| {
                        panic!("ошибка разбора для '{}': {:?}", $input, e)
                    });
                    let result = expr.evaluate().unwrap_or_else(|e| {
                        panic!("ошибка вычисления для '{}': {:?}", $input, e)
                    });
                    assert_eq!(result, $expected, "ввод: '{}'", $input);
                }
            )*
        };
    }

    eval_tests! {
        // Литералы
        eval_zero: "0" => 0,
        eval_positive: "42" => 42,
        eval_i64_max: "9223372036854775807" => i64::MAX,

        // Базовые операции
        eval_add: "1 + 2" => 3,
        eval_sub: "5 - 3" => 2,
        eval_mul: "3 * 4" => 12,
        eval_div: "10 / 2" => 5,

        // Приоритет
        eval_add_mul: "2 + 3 * 4" => 14,
        eval_mixed_precedence: "1 + 2 * 3 - 4 / 2" => 5,

        // Левоассоциативность
        eval_sub_left_assoc: "10 - 5 - 2" => 3,
        eval_div_left_assoc: "24 / 4 / 2" => 3,

        // Скобки
        eval_parens: "(2 + 3) * 4" => 20,
        eval_parens_nested: "((1 + 2))" => 3,

        // Унарные операторы
        eval_unary_neg: "-5" => -5,
        eval_unary_plus: "+5" => 5,
        eval_double_neg: "--5" => 5,
        eval_neg_in_expr: "3 * -2" => -6,

        // i64::MIN - особый случай!
        eval_i64_min: "-9223372036854775808" => i64::MIN,
        eval_i64_min_expr: "0 + -9223372036854775808" => i64::MIN,
        eval_i64_min_in_parens: "(-9223372036854775808)" => i64::MIN,

        // Сложные выражения
        eval_complex: "-(2 + 3) * 4 - 5" => -25,
        eval_double_negative: "1 - -2" => 3,
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Тесты структуры AST
    // ─────────────────────────────────────────────────────────────────────────

    #[test]
    fn ast_negative_literal() {
        // -5 создаёт Literal(-5), а не Unary(Neg, Literal(5))
        assert_eq!(parse("-5").unwrap(), Expr::literal(-5));
    }

    #[test]
    fn ast_i64_min_is_literal() {
        // i64::MIN создаёт один литерал
        assert_eq!(
            parse("-9223372036854775808").unwrap(),
            Expr::literal(i64::MIN)
        );
    }

    #[test]
    fn ast_double_neg_is_unary() {
        // --5 это Unary(Neg, Literal(-5))
        assert_eq!(
            parse("--5").unwrap(),
            Expr::unary(UnaryOp::Neg, Expr::literal(-5))
        );
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Тесты обработки ошибок
    // ─────────────────────────────────────────────────────────────────────────

    #[test]
    fn error_empty_input() {
        assert!(matches!(parse(""), Err(ParseError::UnexpectedEof)));
    }

    #[test]
    fn error_unclosed_paren() {
        let err = parse("(1 + 2").unwrap_err();
        assert!(matches!(err, ParseError::UnclosedParen { open_pos: 0 }));
    }

    #[test]
    fn error_unclosed_nested() {
        let err = parse("((1 + 2)").unwrap_err();
        assert!(matches!(err, ParseError::UnclosedParen { open_pos: 0 }));
    }

    #[test]
    fn error_unexpected_token_has_position() {
        let err = parse("1 + )").unwrap_err();
        if let ParseError::UnexpectedToken { pos, .. } = err {
            assert_eq!(pos, 4);
        } else {
            panic!("expected UnexpectedToken, got {:?}", err);
        }
    }

    #[test]
    fn error_number_out_of_range() {
        // Число больше i64::MAX без знака минус
        let err = parse("9223372036854775808").unwrap_err();
        assert!(matches!(err, ParseError::NumberOutOfRange { pos: 0 }));
    }

    #[test]
    fn error_number_way_out_of_range() {
        // Число больше i64::MIN по модулю
        let err = parse("-9223372036854775809").unwrap_err();
        assert!(matches!(err, ParseError::NumberOutOfRange { pos: 1 }));
    }

    #[test]
    fn error_position_reported() {
        let err = parse("1 @ 2").unwrap_err();
        assert_eq!(err.position(), Some(2));

        let err = parse("(1 + 2").unwrap_err();
        assert_eq!(err.position(), Some(0));
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Тесты ошибок вычисления
    // ─────────────────────────────────────────────────────────────────────────

    #[test]
    fn eval_error_division_by_zero() {
        let expr = parse("1 / 0").unwrap();
        assert_eq!(expr.evaluate(), Err(EvalError::DivisionByZero));
    }

    #[test]
    fn eval_error_overflow() {
        let expr = parse("9223372036854775807 + 1").unwrap();
        assert_eq!(expr.evaluate(), Err(EvalError::Overflow));
    }

    #[test]
    fn eval_i64_min_neg_overflows() {
        // -(-9223372036854775808) = переполнение
        let expr = parse("-(-9223372036854775808)").unwrap();
        assert_eq!(expr.evaluate(), Err(EvalError::Overflow));
    }
}

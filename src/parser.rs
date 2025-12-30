//! Рекурсивный нисходящий парсер арифметических выражений.
//!
//! Преобразует поток [`Token`] в дерево выражений ([`Expr`]).
//!
//! # Грамматика
//!
//! Парсер реализует следующую грамматику со стандартным приоритетом операторов:
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
//! // Простая арифметика
//! let expr = parse("2 + 3 * 4").unwrap();
//! assert_eq!(expr.evaluate().unwrap(), 14);
//!
//! // Скобки переопределяют приоритет
//! let expr = parse("(2 + 3) * 4").unwrap();
//! assert_eq!(expr.evaluate().unwrap(), 20);
//!
//! // Унарные операторы
//! let expr = parse("-5 + 3").unwrap();
//! assert_eq!(expr.evaluate().unwrap(), -2);
//! ```

use std::iter::Peekable;

use thiserror::Error;

use crate::expression::{BinaryOp, Expr, UnaryOp};
use crate::token::{Token, TokenError, Tokenizer};

/// Ошибки, возникающие при разборе выражения.
#[derive(Error, Debug, PartialEq, Eq)]
pub enum ParseError {
    /// Неожиданный конец ввода.
    #[error("неожиданный конец ввода")]
    UnexpectedEof,

    /// Встречен неожиданный токен.
    #[error("неожиданный токен: {0:?}")]
    UnexpectedToken(Token),

    /// Ошибка, переданная от токенизатора.
    #[error("ошибка токенизатора: {0}")]
    TokenError(#[from] TokenError),

    /// Отсутствует закрывающая скобка.
    #[error("отсутствует закрывающая скобка")]
    UnclosedParen,
}

/// Рекурсивный нисходящий парсер арифметических выражений.
///
/// Оборачивает [`Tokenizer`] и строит дерево [`Expr`] согласно
/// грамматике, описанной в [документации модуля](self).
///
/// # Пример
///
/// ```
/// use calculator_rs::parser::Parser;
///
/// let expr = Parser::new("1 + 2 * 3").parse().unwrap();
/// assert_eq!(expr.evaluate().unwrap(), 7);
/// ```
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
    /// Потребляет весь ввод; возвращает ошибку, если после корректного
    /// выражения остались лишние токены.
    ///
    /// # Ошибки
    ///
    /// Возвращает [`ParseError`], если:
    /// - Ввод пуст ([`ParseError::UnexpectedEof`])
    /// - Синтаксис некорректен ([`ParseError::UnexpectedToken`])
    /// - Скобки не сбалансированы ([`ParseError::UnclosedParen`])
    /// - Токенизатор обнаружил ошибку ([`ParseError::TokenError`])
    ///
    /// # Пример
    ///
    /// ```
    /// use calculator_rs::parser::Parser;
    ///
    /// let expr = Parser::new("(1 + 2) * 3").parse().unwrap();
    /// assert_eq!(expr.evaluate().unwrap(), 9);
    /// ```
    pub fn parse(mut self) -> Result<Expr, ParseError> {
        let expr = self.expr()?;

        // Убеждаемся, что не осталось лишних токенов
        match self.tokens.next() {
            None => Ok(expr),
            Some(Ok(token)) => Err(ParseError::UnexpectedToken(token)),
            Some(Err(err)) => Err(err.into()),
        }
    }

    /// Подглядывает следующий токен без его потребления.
    fn peek(&mut self) -> Option<&Result<Token, TokenError>> {
        self.tokens.peek()
    }

    /// Потребляет и возвращает следующий токен.
    fn advance(&mut self) -> Option<Result<Token, TokenError>> {
        self.tokens.next()
    }

    /// Пытается сопоставить один из заданных символов.
    ///
    /// При успехе потребляет токен и возвращает совпавший символ.
    fn match_symbol(&mut self, expected: &[char]) -> Option<char> {
        let matched = match self.peek()? {
            Ok(Token::Symbol(c)) if expected.contains(c) => *c,
            _ => return None,
        };
        self.advance();
        Some(matched)
    }

    /// Разбирает: `expr = term (('+' | '-') term)*`
    fn expr(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.term()?;

        while let Some(op) = self.match_symbol(&['+', '-']) {
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

        while let Some(op) = self.match_symbol(&['*', '/']) {
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
        if let Some(op) = self.match_symbol(&['+', '-']) {
            let child = self.factor()?;
            let kind = match op {
                '+' => UnaryOp::Plus,
                '-' => UnaryOp::Neg,
                _ => unreachable!(),
            };
            return Ok(Expr::unary(kind, child));
        }

        self.factor()
    }

    /// Разбирает: `factor = NUMBER | '(' expr ')'`
    fn factor(&mut self) -> Result<Expr, ParseError> {
        let token = self.advance().ok_or(ParseError::UnexpectedEof)??;

        match token {
            Token::Number(n) => Ok(Expr::literal(n)),
            Token::OpenBracket => {
                let inner = self.expr()?;
                match self.advance() {
                    Some(Ok(Token::CloseBracket)) => Ok(inner),
                    Some(Ok(t)) => Err(ParseError::UnexpectedToken(t)),
                    Some(Err(e)) => Err(e.into()),
                    None => Err(ParseError::UnclosedParen),
                }
            }
            t => Err(ParseError::UnexpectedToken(t)),
        }
    }
}

/// Разбирает строку в дерево выражения.
///
/// Это удобная функция, которая создаёт [`Parser`] и вызывает [`Parser::parse`].
///
/// # Ошибки
///
/// Возвращает [`ParseError`] при некорректном синтаксисе или ошибках токенизации.
///
/// # Примеры
///
/// ```
/// use calculator_rs::parser::parse;
///
/// assert_eq!(parse("2 + 2").unwrap().evaluate().unwrap(), 4);
/// assert_eq!(parse("10 - 3 * 2").unwrap().evaluate().unwrap(), 4);
/// assert_eq!(parse("(10 - 3) * 2").unwrap().evaluate().unwrap(), 14);
/// ```
pub fn parse(input: &str) -> Result<Expr, ParseError> {
    Parser::new(input).parse()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expression::EvalError;

    // ─────────────────────────────────────────────────────────────────────────
    // Параметризованные тесты вычислений через макрос
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
        eval_large_number: "1000000" => 1_000_000,

        // Базовые бинарные операции
        eval_add: "1 + 2" => 3,
        eval_sub: "5 - 3" => 2,
        eval_mul: "3 * 4" => 12,
        eval_div: "10 / 2" => 5,
        eval_div_truncates: "7 / 3" => 2,

        // Приоритет: * и / связывают сильнее, чем + и -
        eval_add_mul: "2 + 3 * 4" => 14,
        eval_mul_add: "2 * 3 + 4" => 10,
        eval_sub_div: "10 - 8 / 2" => 6,
        eval_mixed_precedence: "1 + 2 * 3 - 4 / 2" => 5,

        // Левоассоциативность
        eval_sub_left_assoc: "10 - 5 - 2" => 3,      // (10-5)-2 = 3, не 10-(5-2) = 7
        eval_div_left_assoc: "24 / 4 / 2" => 3,      // (24/4)/2 = 3, не 24/(4/2) = 12
        eval_add_chain: "1 + 2 + 3 + 4" => 10,
        eval_mul_chain: "2 * 3 * 4" => 24,

        // Скобки
        eval_parens_add_mul: "(2 + 3) * 4" => 20,
        eval_parens_nested: "((1 + 2))" => 3,
        eval_parens_complex: "((2 + 3) * (4 - 1))" => 15,
        eval_parens_single: "(42)" => 42,
        eval_parens_around_all: "(1 + 2 * 3)" => 7,

        // Унарные операторы
        eval_unary_neg: "-5" => -5,
        eval_unary_plus: "+5" => 5,
        eval_unary_neg_in_expr: "3 * -2" => -6,
        eval_unary_plus_in_expr: "3 * +2" => 6,
        eval_unary_neg_paren: "-(2 + 3)" => -5,
        eval_unary_neg_neg: "-(-5)" => 5,
        eval_unary_plus_neg: "+(-5)" => -5,

        // Сложные выражения
        eval_complex1: "-(2 + 3) * 4 - 5" => -25,
        eval_complex2: "(1 + 2) * (3 + 4)" => 21,
        eval_complex3: "10 + 20 - 5 * 2 / 2" => 25,
        eval_complex4: "100 / (2 + 3) / 4" => 5,
        eval_complex5: "1 + -2 * 3" => -5,

        // Обработка пробелов
        eval_no_spaces: "1+2*3" => 7,
        eval_extra_spaces: "  1   +   2  " => 3,
        eval_mixed_whitespace: " ( 1 + 2 ) * 3 " => 9,

        // Граничные случаи
        eval_negative_result: "1 - 10" => -9,
        eval_double_negative: "1 - -2" => 3,
        eval_zero_result: "5 - 5" => 0,
        eval_zero_mul: "0 * 100" => 0,
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Тесты структуры AST
    // ─────────────────────────────────────────────────────────────────────────

    #[test]
    fn ast_literal() {
        assert_eq!(parse("42").unwrap(), Expr::literal(42));
    }

    #[test]
    fn ast_binary_add() {
        assert_eq!(
            parse("1 + 2").unwrap(),
            Expr::binary(BinaryOp::Add, Expr::literal(1), Expr::literal(2))
        );
    }

    #[test]
    fn ast_unary_neg() {
        assert_eq!(
            parse("-5").unwrap(),
            Expr::unary(UnaryOp::Neg, Expr::literal(5))
        );
    }

    #[test]
    fn ast_precedence_structure() {
        // 2 + 3 * 4 должно разобраться как Add(2, Mul(3, 4))
        assert_eq!(
            parse("2 + 3 * 4").unwrap(),
            Expr::binary(
                BinaryOp::Add,
                Expr::literal(2),
                Expr::binary(BinaryOp::Mul, Expr::literal(3), Expr::literal(4))
            )
        );
    }

    #[test]
    fn ast_left_associativity() {
        // 1 - 2 - 3 должно разобраться как Sub(Sub(1, 2), 3)
        assert_eq!(
            parse("1 - 2 - 3").unwrap(),
            Expr::binary(
                BinaryOp::Sub,
                Expr::binary(BinaryOp::Sub, Expr::literal(1), Expr::literal(2)),
                Expr::literal(3)
            )
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
    fn error_whitespace_only() {
        assert!(matches!(parse("   "), Err(ParseError::UnexpectedEof)));
    }

    #[test]
    fn error_unclosed_paren() {
        assert!(matches!(parse("(1 + 2"), Err(ParseError::UnclosedParen)));
    }

    #[test]
    fn error_unclosed_nested_paren() {
        assert!(matches!(parse("((1 + 2)"), Err(ParseError::UnclosedParen)));
    }

    #[test]
    fn error_unexpected_close_paren() {
        assert!(matches!(
            parse(")"),
            Err(ParseError::UnexpectedToken(Token::CloseBracket))
        ));
    }

    #[test]
    fn error_close_paren_in_expr() {
        assert!(matches!(
            parse("1 + )"),
            Err(ParseError::UnexpectedToken(Token::CloseBracket))
        ));
    }

    #[test]
    fn error_trailing_number() {
        assert!(matches!(
            parse("1 2"),
            Err(ParseError::UnexpectedToken(Token::Number(2)))
        ));
    }

    #[test]
    fn error_trailing_operator() {
        assert!(matches!(parse("1 +"), Err(ParseError::UnexpectedEof)));
    }

    #[test]
    fn error_leading_mul() {
        assert!(matches!(
            parse("* 2"),
            Err(ParseError::UnexpectedToken(Token::Symbol('*')))
        ));
    }

    #[test]
    fn error_unknown_symbol() {
        assert!(matches!(parse("1 @ 2"), Err(ParseError::TokenError(_))));
    }

    #[test]
    fn error_extra_close_paren() {
        assert!(matches!(
            parse("(1 + 2))"),
            Err(ParseError::UnexpectedToken(Token::CloseBracket))
        ));
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Тесты ошибок вычисления (разбор успешен, вычисление неудачно)
    // ─────────────────────────────────────────────────────────────────────────

    #[test]
    fn eval_error_division_by_zero() {
        let expr = parse("1 / 0").unwrap();
        assert_eq!(expr.evaluate(), Err(EvalError::DivisionByZero));
    }

    #[test]
    fn eval_error_division_by_zero_expr() {
        let expr = parse("10 / (5 - 5)").unwrap();
        assert_eq!(expr.evaluate(), Err(EvalError::DivisionByZero));
    }

    #[test]
    fn eval_error_overflow_add() {
        let input = format!("{} + 1", i64::MAX);
        let expr = parse(&input).unwrap();
        assert_eq!(expr.evaluate(), Err(EvalError::Overflow));
    }

    #[test]
    fn eval_error_overflow_mul() {
        let input = format!("{} * 2", i64::MAX);
        let expr = parse(&input).unwrap();
        assert_eq!(expr.evaluate(), Err(EvalError::Overflow));
    }

    #[test]
    fn eval_error_overflow_neg() {
        let input = format!("-({})", i64::MIN);
        let expr = parse(&input).unwrap();
        assert_eq!(expr.evaluate(), Err(EvalError::Overflow));
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Граничные случаи, которые могут быть неочевидны
    // ─────────────────────────────────────────────────────────────────────────

    #[test]
    fn double_plus_is_unary_plus() {
        // "1 + + 2" разбирается как "1 + (+2)", что равно 3
        let expr = parse("1 + + 2").unwrap();
        assert_eq!(expr.evaluate().unwrap(), 3);
    }

    #[test]
    fn minus_minus_is_add() {
        // "1 - - 2" разбирается как "1 - (-2)", что равно 3
        let expr = parse("1 - - 2").unwrap();
        assert_eq!(expr.evaluate().unwrap(), 3);
    }
}

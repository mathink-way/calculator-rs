//! # calculator_rs
//!
//! Простой консольный калькулятор арифметических выражений.
//!
//! Поддерживает:
//! - Целые числа (i64), включая i64::MIN
//! - Бинарные операции: `+`, `-`, `*`, `/`
//! - Унарные операции: `+`, `-`
//! - Скобки для группировки
//!
//! # Пример использования
//!
//! ```
//! use calculator_rs::evaluate;
//!
//! assert_eq!(evaluate("2 + 2").unwrap(), 4);
//! assert_eq!(evaluate("-9223372036854775808").unwrap(), i64::MIN);
//! ```

pub mod expression;
pub mod parser;
pub mod token;

use std::io::{self, BufRead, Write};

/// Общий тип ошибки калькулятора.
#[derive(Debug, thiserror::Error)]
pub enum CalcError {
    /// Ошибка разбора выражения.
    #[error("{0}")]
    Parse(#[from] parser::ParseError),

    /// Ошибка вычисления (деление на ноль, переполнение).
    #[error("{0}")]
    Eval(#[from] expression::EvalError),
}

impl CalcError {
    /// Возвращает позицию ошибки в исходной строке, если она известна.
    #[must_use]
    pub const fn position(&self) -> Option<usize> {
        match self {
            Self::Parse(pe) => pe.position(),
            Self::Eval(_) => None,
        }
    }
}

/// Вычисляет строковое выражение и возвращает результат.
///
/// # Ошибки
///
/// Возвращает [`CalcError`] при ошибках парсинга или вычисления.
///
/// # Примеры
///
/// ```
/// use calculator_rs::evaluate;
///
/// assert_eq!(evaluate("2 + 2").unwrap(), 4);
/// assert_eq!(evaluate("(1 + 2) * 3").unwrap(), 9);
/// assert!(evaluate("1 / 0").is_err());
/// ```
pub fn evaluate(input: &str) -> Result<i64, CalcError> {
    let expr = parser::parse(input)?;
    let result = expr.evaluate()?;
    Ok(result)
}

/// Запускает интерактивный REPL-калькулятор.
///
/// Читает выражения из stdin, вычисляет их и выводит результат в stdout.
/// Для выхода введите `q`, `quit`, `exit` или нажмите Ctrl+D.
///
/// # Ошибки
///
/// Возвращает [`io::Error`] при ошибках чтения/записи.
pub fn run() -> io::Result<()> {
    let stdin = io::stdin();
    let mut stdout = io::stdout();

    println!("Калькулятор. Введите выражение или 'q' для выхода.");

    for line in stdin.lock().lines() {
        let line = line?;
        let input = line.trim();

        if input.eq_ignore_ascii_case("q") || input == "exit" || input == "quit" {
            break;
        }

        if input.is_empty() {
            print!("> ");
            stdout.flush()?;
            continue;
        }

        match evaluate(input) {
            Ok(result) => println!("{result}"),
            Err(e) => print_error_with_context(input, &e),
        }

        print!("> ");
        stdout.flush()?;
    }

    println!("До свидания!");
    Ok(())
}

/// Выводит ошибку с указанием позиции в исходной строке.
fn print_error_with_context(input: &str, error: &CalcError) {
    if let Some(pos) = error.position() {
        // Показываем исходную строку и указатель на ошибку
        println!("  {input}");
        println!("  {}^", " ".repeat(pos));
        println!("Ошибка: {error}");
    } else {
        println!("Ошибка: {error}");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn evaluate_simple() {
        assert_eq!(evaluate("1 + 2").unwrap(), 3);
        assert_eq!(evaluate("10 - 3").unwrap(), 7);
        assert_eq!(evaluate("4 * 5").unwrap(), 20);
        assert_eq!(evaluate("15 / 3").unwrap(), 5);
    }

    #[test]
    fn evaluate_i64_min() {
        assert_eq!(evaluate("-9223372036854775808").unwrap(), i64::MIN);
    }

    #[test]
    fn evaluate_i64_max() {
        assert_eq!(evaluate("9223372036854775807").unwrap(), i64::MAX);
    }

    #[test]
    fn evaluate_errors() {
        assert!(matches!(evaluate("1 / 0"), Err(CalcError::Eval(_))));
        assert!(matches!(evaluate("1 +"), Err(CalcError::Parse(_))));
        assert!(matches!(evaluate(""), Err(CalcError::Parse(_))));
    }

    #[test]
    fn error_has_position() {
        let err = evaluate("1 @ 2").unwrap_err();
        assert_eq!(err.position(), Some(2));

        let err = evaluate("(1 + 2").unwrap_err();
        assert_eq!(err.position(), Some(0));

        // Ошибка вычисления не имеет позиции
        let err = evaluate("1 / 0").unwrap_err();
        assert_eq!(err.position(), None);
    }

    #[test]
    fn number_out_of_range_error() {
        // Без минуса - не влезает в i64
        let err = evaluate("9223372036854775808").unwrap_err();
        assert!(matches!(
            err,
            CalcError::Parse(parser::ParseError::NumberOutOfRange { .. })
        ));

        // С минусом но слишком большое
        let err = evaluate("-9223372036854775809").unwrap_err();
        assert!(matches!(
            err,
            CalcError::Parse(parser::ParseError::NumberOutOfRange { .. })
        ));
    }
}

//! Простое дерево выражений с вычислением (evaluate).
//!
//! Поддерживает литералы i64, унарные операции + и - и бинарные +, -, *, /.
//!
//! # Примеры
//!
//! ```
//! use calculator_rs::expression::{Expr, UnaryOp, BinaryOp};
//!
//! let e = Expr::binary(BinaryOp::Add, Expr::literal(2), Expr::literal(3));
//! assert_eq!(e.evaluate(), Ok(5));
//!
//! let e = Expr::unary(UnaryOp::Neg, Expr::literal(5));
//! assert_eq!(e.evaluate(), Ok(-5));
//! ```

use thiserror::Error;

/// Ошибки при вычислении выражения.
#[derive(Error, Debug, Clone, PartialEq, Eq)]
pub enum EvalError {
    /// Деление на ноль.
    #[error("деление на ноль")]
    DivisionByZero,
    /// Целочисленное переполнение.
    #[error("переполнение")]
    Overflow,
}

/// Унарные операции.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    /// Унарный плюс (идентичность).
    Plus,
    /// Унарный минус (отрицание).
    Neg,
}

impl UnaryOp {
    /// Применить унарную операцию к значению.
    ///
    /// # Ошибки
    ///
    /// Возвращает [`EvalError::Overflow`] при переполнении (например, `-i64::MIN`).
    pub fn apply(self, value: i64) -> Result<i64, EvalError> {
        match self {
            Self::Plus => Ok(value),
            Self::Neg => value.checked_neg().ok_or(EvalError::Overflow),
        }
    }
}

/// Бинарные операции.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    /// Сложение.
    Add,
    /// Вычитание.
    Sub,
    /// Умножение.
    Mul,
    /// Целочисленное деление.
    Div,
}

impl BinaryOp {
    /// Применить бинарную операцию к операндам.
    ///
    /// # Ошибки
    ///
    /// - [`EvalError::DivisionByZero`] при делении на ноль.
    /// - [`EvalError::Overflow`] при переполнении.
    pub fn apply(self, left: i64, right: i64) -> Result<i64, EvalError> {
        match self {
            Self::Add => left.checked_add(right).ok_or(EvalError::Overflow),
            Self::Sub => left.checked_sub(right).ok_or(EvalError::Overflow),
            Self::Mul => left.checked_mul(right).ok_or(EvalError::Overflow),
            Self::Div => {
                if right == 0 {
                    Err(EvalError::DivisionByZero)
                } else {
                    left.checked_div(right).ok_or(EvalError::Overflow)
                }
            }
        }
    }
}

/// Дерево выражений.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    /// Литеральное целое значение.
    Literal(i64),
    /// Унарная операция.
    Unary { kind: UnaryOp, child: Box<Expr> },
    /// Бинарная операция.
    Binary {
        kind: BinaryOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
}

impl Expr {
    /// Создать литерал.
    #[must_use]
    pub const fn literal(value: i64) -> Self {
        Self::Literal(value)
    }

    /// Создать унарное выражение.
    #[must_use]
    pub fn unary(kind: UnaryOp, child: Self) -> Self {
        Self::Unary {
            kind,
            child: Box::new(child),
        }
    }

    /// Создать бинарное выражение.
    #[must_use]
    pub fn binary(kind: BinaryOp, left: Self, right: Self) -> Self {
        Self::Binary {
            kind,
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    /// Вычислить значение выражения.
    ///
    /// Выполняет рекурсивную оценку дерева. Деление — целочисленное.
    ///
    /// # Ошибки
    ///
    /// - [`EvalError::DivisionByZero`] при делении на ноль.
    /// - [`EvalError::Overflow`] при переполнении.
    pub fn evaluate(&self) -> Result<i64, EvalError> {
        match self {
            Self::Literal(v) => Ok(*v),
            Self::Unary { kind, child } => kind.apply(child.evaluate()?),
            Self::Binary { kind, left, right } => {
                let l = left.evaluate()?;
                let r = right.evaluate()?;
                kind.apply(l, r)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn literal_eval() {
        assert_eq!(Expr::literal(0).evaluate(), Ok(0));
        assert_eq!(Expr::literal(42).evaluate(), Ok(42));
        assert_eq!(Expr::literal(-7).evaluate(), Ok(-7));
    }

    #[test]
    fn unary_plus_neg() {
        let e = Expr::unary(UnaryOp::Plus, Expr::literal(5));
        assert_eq!(e.evaluate(), Ok(5));

        let e = Expr::unary(UnaryOp::Neg, Expr::literal(5));
        assert_eq!(e.evaluate(), Ok(-5));
    }

    #[test]
    fn binary_arithmetic() {
        let a = Expr::literal(10);
        let b = Expr::literal(3);

        assert_eq!(
            Expr::binary(BinaryOp::Add, a.clone(), b.clone()).evaluate(),
            Ok(13)
        );
        assert_eq!(
            Expr::binary(BinaryOp::Sub, a.clone(), b.clone()).evaluate(),
            Ok(7)
        );
        assert_eq!(
            Expr::binary(BinaryOp::Mul, a.clone(), b.clone()).evaluate(),
            Ok(30)
        );
        assert_eq!(Expr::binary(BinaryOp::Div, a, b).evaluate(), Ok(3));
    }

    #[test]
    fn nested_expressions() {
        // (2 + 3) * -(4 - 6) = 5 * -(-2) = 5 * 2 = 10
        let expr = Expr::binary(
            BinaryOp::Mul,
            Expr::binary(BinaryOp::Add, Expr::literal(2), Expr::literal(3)),
            Expr::unary(
                UnaryOp::Neg,
                Expr::binary(BinaryOp::Sub, Expr::literal(4), Expr::literal(6)),
            ),
        );
        assert_eq!(expr.evaluate(), Ok(10));
    }

    #[test]
    fn div_by_zero_returns_error() {
        let expr = Expr::binary(BinaryOp::Div, Expr::literal(1), Expr::literal(0));
        assert_eq!(expr.evaluate(), Err(EvalError::DivisionByZero));
    }

    #[test]
    fn overflow_add() {
        let expr = Expr::binary(BinaryOp::Add, Expr::literal(i64::MAX), Expr::literal(1));
        assert_eq!(expr.evaluate(), Err(EvalError::Overflow));
    }

    #[test]
    fn overflow_sub() {
        let expr = Expr::binary(BinaryOp::Sub, Expr::literal(i64::MIN), Expr::literal(1));
        assert_eq!(expr.evaluate(), Err(EvalError::Overflow));
    }

    #[test]
    fn overflow_mul() {
        let expr = Expr::binary(BinaryOp::Mul, Expr::literal(i64::MAX), Expr::literal(2));
        assert_eq!(expr.evaluate(), Err(EvalError::Overflow));
    }

    #[test]
    fn overflow_unary_neg() {
        let expr = Expr::unary(UnaryOp::Neg, Expr::literal(i64::MIN));
        assert_eq!(expr.evaluate(), Err(EvalError::Overflow));
    }

    #[test]
    fn ops_apply_match() {
        assert_eq!(UnaryOp::Plus.apply(5), Ok(5));
        assert_eq!(UnaryOp::Neg.apply(5), Ok(-5));

        assert_eq!(BinaryOp::Add.apply(2, 3), Ok(5));
        assert_eq!(BinaryOp::Sub.apply(5, 3), Ok(2));
        assert_eq!(BinaryOp::Mul.apply(4, 3), Ok(12));
        assert_eq!(BinaryOp::Div.apply(7, 2), Ok(3));
    }

    #[test]
    fn eq_and_clone() {
        let a = Expr::binary(BinaryOp::Add, Expr::literal(1), Expr::literal(2));
        let b = a.clone();
        assert_eq!(a, b);
    }
}

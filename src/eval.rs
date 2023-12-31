use std::fmt::Display;

use crate::expr::Expr;

#[derive(Debug)]
pub enum RuntimeError {
    Uncallable,
    Unprintable,
    Unaddable,
    UnknownFunction(String),
    WrongNumArgs { want: usize, got: usize },
}

impl Display for RuntimeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RuntimeError::Uncallable => write!(f, "Uncallable"),
            RuntimeError::Unprintable => write!(f, "Unprintable"),
            RuntimeError::Unaddable => write!(f, "Unaddable"),
            RuntimeError::UnknownFunction(s) => write!(f, "Unknown function {}", s),
            RuntimeError::WrongNumArgs { want, got } => {
                write!(f, "Wanted {} args, but got {}", want, got)
            }
        }
    }
}

pub fn eval(expr: Expr) -> Result<Expr, RuntimeError> {
    match expr {
        Expr::Int(_) => Ok(expr),
        Expr::String(_) => Ok(expr),
        Expr::Symbol(_) => Ok(expr),
        Expr::Quoted(_) => Ok(expr),
        Expr::Application(boxed_expr, args) => match *boxed_expr {
            Expr::Symbol(func_name) => match func_name.as_str() {
                "quote" => Ok(Expr::Quoted(args)),
                "cond" => builtin_cond(args),
                "print" => builtin_print(args),
                "add" => builtin_add(args),
                _ => Err(RuntimeError::UnknownFunction(func_name)),
            },
            _ => Err(RuntimeError::Uncallable),
        },
    }
}

fn builtin_cond(args: Vec<Expr>) -> Result<Expr, RuntimeError> {
    const NUM_ARGS: usize = 3;
    if args.len() != NUM_ARGS {
        return Err(RuntimeError::WrongNumArgs {
            want: NUM_ARGS,
            got: args.len(),
        });
    }

    let mut args = args;
    let e2 = args.pop().unwrap();
    let e1 = args.pop().unwrap();
    let selector = args.pop().unwrap();

    match eval(selector)? {
        Expr::Int(0) => eval(e2),
        _ => eval(e1),
    }
}

fn builtin_print(args: Vec<Expr>) -> Result<Expr, RuntimeError> {
    let mut pieces = Vec::new();
    for arg in args {
        match eval(arg)? {
            Expr::Int(n) => {
                pieces.push(format!("{}", n));
            }
            Expr::String(s) => {
                pieces.push(format!("{}", s));
            }
            Expr::Symbol(s) => {
                pieces.push(format!("{}", s));
            }
            Expr::Quoted(expr) => {
                pieces.push(format!("{:?}", expr));
            }
            Expr::Application(_, _) => {
                return Err(RuntimeError::Unprintable);
            }
        }
    }
    let joined = pieces.join(" ");
    println!("{}", joined);
    Ok(Expr::String(joined))
}

fn builtin_add(args: Vec<Expr>) -> Result<Expr, RuntimeError> {
    let mut sum = 0;
    for arg in args {
        match eval(arg)? {
            Expr::Int(n) => {
                sum += n;
            }
            _ => {
                return Err(RuntimeError::Unaddable);
            }
        }
    }
    Ok(Expr::Int(sum))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cond() {
        let expr = Expr::parse_str("(cond 0 \"truth\" \"lies\")").unwrap();
        let expr = eval(expr).unwrap();
        assert_eq!(expr, Expr::String(String::from("lies")));

        let expr = Expr::parse_str("(cond 1 \"truth\" \"lies\")").unwrap();
        let expr = eval(expr).unwrap();
        assert_eq!(expr, Expr::String(String::from("truth")));

        let expr = Expr::parse_str("(cond 2 \"truth\" \"lies\")").unwrap();
        let expr = eval(expr).unwrap();
        assert_eq!(expr, Expr::String(String::from("truth")));

        let expr = Expr::parse_str("(cond \"x\" \"truth\" \"lies\")").unwrap();
        let expr = eval(expr).unwrap();
        assert_eq!(expr, Expr::String(String::from("truth")));
    }

    #[test]
    fn test_cond_complex_selector() {
        let expr = Expr::parse_str("(cond (add 0 0) \"truth\" \"lies\")").unwrap();
        let expr = eval(expr).unwrap();
        assert_eq!(expr, Expr::String(String::from("lies")));

        let expr = Expr::parse_str("(cond (add 1 0) \"truth\" \"lies\")").unwrap();
        let expr = eval(expr).unwrap();
        assert_eq!(expr, Expr::String(String::from("truth")));
    }

    #[test]
    fn test_cond_complex_result() {
        let expr = Expr::parse_str("(cond 1 (cond 0 \"a\" \"b\") \"c\")").unwrap();
        let expr = eval(expr).unwrap();
        assert_eq!(expr, Expr::String(String::from("b")));

        let expr = Expr::parse_str("(cond 0 \"c\" (cond 0 \"a\" \"b\"))").unwrap();
        let expr = eval(expr).unwrap();
        assert_eq!(expr, Expr::String(String::from("b")));
    }
}

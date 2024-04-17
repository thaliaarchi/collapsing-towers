//! Parsing for a Lisp-like front-end.
//!
//! # Grammar
//!
//! This follows the grammar of popl18/lisp.scala:
//!
//! ```bnf
//! exp ::=
//!     | -?\d+        { s => Num(s) }
//!     | [^\s\(\)'"]+ { s => Sym(s) }
//!     | "'" exp      { s => Pair(Sym("quote"), Pair(s, Sym("."))) }
//!     | "()"         { _ => Sym(".") }
//!     | "(" exps ")" { vs => vs }
//!
//! exps ::=
//!     | exp exps     { v, vs => Pair(v, vs) }
//!     | ε            { _ => Sym(".") }
//!
//! ws ::=
//!     | (\s|;[^\n]*\n?)+
//! ```
//!
//! In this implementation, unlike the original, `+` sign is allowed for
//! integers, `;` is not allowed in symbols, and spaces are allowed in unit.

use std::rc::Rc;
use std::str;

use im_rc::Vector;
use winnow::{
    ascii::{dec_int, multispace1, till_line_ending},
    combinator::{alt, cut_err, delimited, preceded, repeat, separated},
    error::{ContextError, ParseError, StrContext},
    prelude::*,
    token::take_while,
};

use crate::base::{Exp, Val};

// TODO: Questions
// - Why do the authors parse to Val then translate it to Exp, rather than
//   parsing directly to Exp? The language is slightly smaller when considering
//   only Val, but that's just engineering. Are there fundamental reasons?
// - Are the `.` symbols necessary? They seem like an artifact of folding lists,
//   not a structural part of the AST.

pub fn parse(input: &str) -> Result<Rc<Val>, ParseError<&str, ContextError>> {
    delimited(ws0, value, ws0).parse(input)
}

fn value(input: &mut &str) -> PResult<Rc<Val>> {
    alt((
        dec_int.map(Val::num),
        symbol.map(|sym| Val::sym(sym)),
        quote,
        list,
    ))
    .context(StrContext::Label("value"))
    .parse_next(input)
}

fn symbol<'i>(input: &mut &'i str) -> PResult<&'i str> {
    take_while(1.., |ch| {
        ('!'..='~').contains(&ch) && !matches!(ch, '"' | '\'' | '(' | ')' | ';')
    })
    .context(StrContext::Label("symbol"))
    .parse_next(input)
}

fn quote(input: &mut &str) -> PResult<Rc<Val>> {
    preceded(
        ("'", ws0),
        value.map(|v| Val::pair(Val::sym("quote"), Val::pair(v, Val::sym(".")))),
    )
    .context(StrContext::Label("quote"))
    .parse_next(input)
}

fn list(input: &mut &str) -> PResult<Rc<Val>> {
    delimited(
        '(',
        preceded(ws0, list_elements),
        cut_err(preceded(ws0, ')')),
    )
    .context(StrContext::Label("list"))
    .parse_next(input)
}

fn list_elements(input: &mut &str) -> PResult<Rc<Val>> {
    let elems: Vec<_> = separated(0.., value, ws1).parse_next(input)?;
    Ok(elems
        .into_iter()
        .rev()
        .fold(Val::sym("."), |r, l| Val::pair(l, r)))
}

fn ws0(input: &mut &str) -> PResult<()> {
    repeat(0.., ws).parse_next(input)
}

fn ws1(input: &mut &str) -> PResult<()> {
    repeat(1.., ws).parse_next(input)
}

fn ws(input: &mut &str) -> PResult<()> {
    alt((multispace1.void(), (';', till_line_ending).void())).parse_next(input)
}

/// Convert an `Exp` encoded as a `Val` to a proper `Exp`.
pub fn trans(v: &Val, env: Vector<String>) -> Rc<Exp> {
    // TODO:
    // - Port `quote`, `trans`, and `lift-ref` translation.
    // - Refactor list translation to unpack lists into a Vec, then dispatch on
    //   the symbol, then check arity.
    // - Return Result.
    match v {
        Val::Num(n) => Exp::num(*n),
        Val::Sym(s) => match env.iter().enumerate().rev().find(|&(_, x)| x == s) {
            Some((i, _)) => Exp::var(i),
            None => panic!("symbol `{s}` not in environment {env:?}"),
        },
        Val::Pair(l, r) => match (&**l, &**r) {
            (Val::Sym(s), Val::Pair(a, b)) => match &**b {
                // Unary functions
                Val::Sym(b) if b == "." => match &**s {
                    "num?" => Exp::is_num(trans(a, env)),
                    "sym?" => Exp::is_sym(trans(a, env)),
                    "pair?" => Exp::is_pair(trans(a, env)),
                    "car" => Exp::car(trans(a, env)),
                    "cdr" => Exp::cdr(trans(a, env)),
                    "cadr" => Exp::car(Exp::cdr(trans(a, env))),
                    "caddr" => Exp::car(Exp::cdr(Exp::cdr(trans(a, env)))),
                    "cadddr" => Exp::car(Exp::cdr(Exp::cdr(Exp::cdr(trans(a, env))))),
                    "lift" => Exp::lift(trans(a, env)),
                    "nolift" => trans(a, env),
                    "quote" => match &**a {
                        Val::Sym(a) => Exp::sym(a.clone()),
                        _ => todo!(),
                    },
                    "trans" => todo!(),
                    "lift-rel" => todo!(),
                    _ => panic!("unrecognized unary function `{s}`"),
                },
                Val::Pair(b, c) => match &**c {
                    // Binary functions
                    Val::Sym(c) if c == "." => match &**s {
                        "+" => Exp::add(trans(a, env.clone()), trans(b, env)),
                        "-" => Exp::sub(trans(a, env.clone()), trans(b, env)),
                        "*" => Exp::mul(trans(a, env.clone()), trans(b, env)),
                        "cons" => Exp::cons(trans(a, env.clone()), trans(b, env)),
                        "eq?" => Exp::eq(trans(a, env.clone()), trans(b, env)),
                        "run" => Exp::run(trans(a, env.clone()), trans(b, env)),
                        "log" => Exp::log(trans(a, env.clone()), trans(b, env)),
                        _ => panic!("unrecognized binary function `{s}`"),
                    },
                    Val::Pair(c, d) => match &**d {
                        // Ternary functions
                        Val::Sym(d) if d == "." => match &**s {
                            "let" => match &**a {
                                Val::Sym(a) => {
                                    let mut env2 = env.clone();
                                    env2.push_back(a.clone());
                                    Exp::let_(trans(b, env), trans(c, env2))
                                }
                                _ => panic!("let binding name must be a symbol"),
                            },
                            "lambda" => match (&**a, &**b) {
                                (Val::Sym(a), Val::Sym(b)) => {
                                    let mut env2 = env.clone();
                                    env2.push_back(a.clone());
                                    env2.push_back(b.clone());
                                    Exp::lam(trans(c, env2))
                                }
                                _ => panic!("lambda self and parameter names must be symbols"),
                            },
                            "if" => Exp::if_(
                                trans(a, env.clone()),
                                trans(b, env.clone()),
                                trans(c, env),
                            ),
                            _ => panic!("unrecognized ternary function `{s}"),
                        },
                        _ => panic!("unrecognized value"),
                    },
                    _ => panic!("unrecognized value"),
                },
                _ => panic!("unrecognized value"),
            },
            (a, Val::Pair(b, c)) => match &**c {
                Val::Sym(c) if c == "." => Exp::app(trans(a, env.clone()), trans(b, env)),
                _ => panic!("cannot apply non-binary functions"),
            },
            _ => panic!("unrecognized value"),
        },
        _ => panic!("unrecognized value"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_example() {
        let code = "
            (let code (trans '(lambda _ x (+ x 42)))
              ; hello
              (cons code ()))
        ";
        let parsed = Val::pair(
            Val::sym("let"),
            Val::pair(
                Val::sym("code"),
                Val::pair(
                    Val::pair(
                        Val::sym("trans"),
                        Val::pair(
                            Val::pair(
                                Val::sym("quote"),
                                Val::pair(
                                    Val::pair(
                                        Val::sym("lambda"),
                                        Val::pair(
                                            Val::sym("_"),
                                            Val::pair(
                                                Val::sym("x"),
                                                Val::pair(
                                                    Val::pair(
                                                        Val::sym("+"),
                                                        Val::pair(
                                                            Val::sym("x"),
                                                            Val::pair(Val::num(42), Val::sym(".")),
                                                        ),
                                                    ),
                                                    Val::sym("."),
                                                ),
                                            ),
                                        ),
                                    ),
                                    Val::sym("."),
                                ),
                            ),
                            Val::sym("."),
                        ),
                    ),
                    Val::pair(
                        Val::pair(
                            Val::sym("cons"),
                            Val::pair(Val::sym("code"), Val::pair(Val::sym("."), Val::sym("."))),
                        ),
                        Val::sym("."),
                    ),
                ),
            ),
        );
        assert_eq!(parse(code), Ok(parsed));
    }
}

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
    Translator {
        list: Vec::with_capacity(3),
    }
    .trans(v, env)
}

impl Val {
    pub fn unfold_list(&self, list: &mut Vec<Rc<Val>>) {
        let mut v = self;
        loop {
            match &*v {
                Val::Pair(a, b) => {
                    list.push(a.clone());
                    v = &**b;
                }
                Val::Sym(s) if s == "." => break,
                _ => panic!("unexpected value in list"),
            }
        }
    }
}

struct Translator {
    list: Vec<Rc<Val>>,
}

impl Translator {
    fn trans(&mut self, v: &Val, env: Vector<String>) -> Rc<Exp> {
        // TODO:
        // - Port `quote`, `trans`, and `lift-ref` translation.
        // - Return Result.

        // Extract the values from `self.list` and pass them to the expression.
        // Only one list is needed for the entire translation, and this pattern
        // keeps the borrow checker happy, yet is optimized away.
        macro_rules! unpack_list(($len:literal, |$($a:ident),+| $e:expr) => {
            if self.list.len() == $len {
                let mut it = self.list.drain(..);
                $(let $a = &*it.next().unwrap();)+
                assert!(it.len() == 0);
                drop(it);
                $e
            } else {
                panic!("arity mismatch");
            }
        });
        macro_rules! op(
            (|$a:ident| $e:expr) => { unpack_list!(1, |$a| $e) };
            (|$a:ident, $b:ident| $e:expr) => { unpack_list!(2, |$a, $b| $e) };
            (|$a:ident, $b:ident, $c:ident| $e:expr) => { unpack_list!(3, |$a, $b, $c| $e) };
        );

        match v {
            Val::Num(n) => Exp::num(*n),
            Val::Sym(s) => match env.iter().enumerate().rev().find(|&(_, x)| x == s) {
                Some((i, _)) => Exp::var(i),
                None => panic!("symbol `{s}` not in environment {env:?}"),
            },

            Val::Pair(a, _) => {
                self.list.clear();
                v.unfold_list(&mut self.list);
                match &**a {
                    Val::Sym(s) => match &**s {
                        // Unary functions
                        "num?" => op!(|a| Exp::is_num(self.trans(a, env))),
                        "sym?" => op!(|a| Exp::is_sym(self.trans(a, env))),
                        "pair?" => op!(|a| Exp::is_pair(self.trans(a, env))),
                        "car" => op!(|a| Exp::car(self.trans(a, env))),
                        "cdr" => op!(|a| Exp::cdr(self.trans(a, env))),
                        "cadr" => op!(|a| Exp::car(Exp::cdr(self.trans(a, env)))),
                        "caddr" => op!(|a| Exp::car(Exp::cdr(Exp::cdr(self.trans(a, env))))),
                        "cadddr" => {
                            op!(|a| Exp::car(Exp::cdr(Exp::cdr(Exp::cdr(self.trans(a, env))))))
                        }
                        "lift" => op!(|a| Exp::lift(self.trans(a, env))),
                        "nolift" => op!(|a| self.trans(a, env)),
                        "quote" => op!(|a| match a {
                            Val::Sym(a) => Exp::sym(a.clone()),
                            _ => todo!(),
                        }),
                        "trans" => op!(|_a| todo!()),
                        "lift-rel" => op!(|_a| todo!()),

                        // Binary functions
                        "+" => {
                            op!(|a, b| Exp::add(self.trans(a, env.clone()), self.trans(b, env)))
                        }
                        "-" => {
                            op!(|a, b| Exp::sub(self.trans(a, env.clone()), self.trans(b, env)))
                        }
                        "*" => {
                            op!(|a, b| Exp::mul(self.trans(a, env.clone()), self.trans(b, env)))
                        }
                        "cons" => {
                            op!(|a, b| Exp::cons(self.trans(a, env.clone()), self.trans(b, env)))
                        }
                        "eq?" => {
                            op!(|a, b| Exp::eq(self.trans(a, env.clone()), self.trans(b, env)))
                        }
                        "run" => {
                            op!(|a, b| Exp::run(self.trans(a, env.clone()), self.trans(b, env)))
                        }
                        "log" => {
                            op!(|a, b| Exp::log(self.trans(a, env.clone()), self.trans(b, env)))
                        }

                        // Ternary functions
                        "let" => op!(|a, b, c| match a {
                            Val::Sym(a) => {
                                let mut env2 = env.clone();
                                env2.push_back(a.clone());
                                Exp::let_(self.trans(b, env), self.trans(c, env2))
                            }
                            _ => panic!("let binding name must be a symbol"),
                        }),
                        "lambda" => op!(|a, b, c| match (a, b) {
                            (Val::Sym(a), Val::Sym(b)) => {
                                let mut env2 = env.clone();
                                env2.push_back(a.clone());
                                env2.push_back(b.clone());
                                Exp::lam(self.trans(c, env2))
                            }
                            _ => panic!("lambda self and parameter names must be symbols"),
                        }),
                        "if" => op!(|a, b, c| Exp::if_(
                            self.trans(a, env.clone()),
                            self.trans(b, env.clone()),
                            self.trans(c, env),
                        )),

                        _ => panic!("unrecognized function: {s}"),
                    },

                    _ => op!(|a, b| Exp::app(self.trans(a, env.clone()), self.trans(b, env))),
                }
            }

            Val::Clo(_, _) | Val::Code(_) => panic!("unrecognized value"),
        }
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

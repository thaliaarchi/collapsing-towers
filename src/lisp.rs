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

use winnow::{
    ascii::{dec_int, multispace1, till_line_ending},
    combinator::{alt, cut_err, delimited, preceded, repeat, separated},
    error::{ContextError, ParseError, StrContext},
    prelude::*,
    token::take_while,
};

use crate::base::{Env, Exp, Val, VarEnv, Vm};

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
pub fn trans(v: &Val, env: VarEnv) -> Rc<Exp> {
    Translator {
        env,
        list: Vec::with_capacity(3),
    }
    .trans(v)
}

pub fn ev(src: &str) -> Rc<Val> {
    // TODO: Handle errors.
    let prog_val = parse(src).unwrap();
    let prog_exp = trans(&prog_val, VarEnv::new());
    let mut vm = Vm::new();
    vm.reifyv(|vm| vm.evalms(&Env::new(), &prog_exp))
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
    env: VarEnv,
    list: Vec<Rc<Val>>,
}

impl Translator {
    fn trans(&mut self, v: &Val) -> Rc<Exp> {
        // TODO:
        // - Port `quote`, `trans`, and `lift-ref` translation.
        // - Return Result.

        // Extract the values from `self.list` and pass them to the expression.
        // Only one list is needed for the entire translation, and this pattern
        // keeps the borrow checker happy, yet is optimized away.
        macro_rules! unpack_list(($len:literal, |$($a:ident),+| $e:expr) => {
            if self.list.len() == $len {
                let mut it = self.list.drain(..);
                $(let $a = it.next().unwrap();)+
                assert!(it.len() == 0);
                drop(it);
                $e
            } else {
                panic!("arity mismatch");
            }
        });
        macro_rules! op(
            (|$a:ident| $e:expr) => { unpack_list!(2, |_f, $a| $e) };
            (|$a:ident, $b:ident| $e:expr) => { unpack_list!(3, |_f, $a, $b| $e) };
            (|$a:ident, $b:ident, $c:ident| $e:expr) => { unpack_list!(4, |_f, $a, $b, $c| $e) };
        );

        match v {
            Val::Num(n) => Exp::num(*n),
            Val::Sym(s) => match self.env.get(s) {
                Some(i) => Exp::var(i),
                None => panic!("symbol `{s}` not in environment {:?}", self.env),
            },

            Val::Pair(a, _) => {
                self.list.clear();
                v.unfold_list(&mut self.list);
                match &**a {
                    Val::Sym(s) => match &**s {
                        // Unary functions
                        "num?" => op!(|a| Exp::is_num(self.trans(&a))),
                        "sym?" => op!(|a| Exp::is_sym(self.trans(&a))),
                        "pair?" => op!(|a| Exp::is_pair(self.trans(&a))),
                        "car" => op!(|a| Exp::car(self.trans(&a))),
                        "cdr" => op!(|a| Exp::cdr(self.trans(&a))),
                        "cadr" => op!(|a| Exp::car(Exp::cdr(self.trans(&a)))),
                        "caddr" => op!(|a| Exp::car(Exp::cdr(Exp::cdr(self.trans(&a))))),
                        "cadddr" => op!(|a| Exp::car(Exp::cdr(Exp::cdr(Exp::cdr(self.trans(&a)))))),
                        "lift" => op!(|a| Exp::lift(self.trans(&a))),
                        "nolift" => op!(|a| self.trans(&a)),
                        "quote" => op!(|a| match &*a {
                            Val::Sym(a) => Exp::sym(a.clone()),
                            _ => Exp::quote(a.clone()),
                        }),
                        "trans" => op!(|a| Exp::trans(a, self.env.clone())),
                        "lift-rel" => op!(|a| Exp::lift_ref(a, self.env.clone())),

                        // Binary functions
                        "+" => op!(|a, b| Exp::add(self.trans(&a), self.trans(&b))),
                        "-" => op!(|a, b| Exp::sub(self.trans(&a), self.trans(&b))),
                        "*" => op!(|a, b| Exp::mul(self.trans(&a), self.trans(&b))),
                        "cons" => op!(|a, b| Exp::cons(self.trans(&a), self.trans(&b))),
                        "eq?" => op!(|a, b| Exp::eq(self.trans(&a), self.trans(&b))),
                        "run" => op!(|a, b| Exp::run(self.trans(&a), self.trans(&b))),
                        "log" => op!(|a, b| Exp::log(self.trans(&a), self.trans(&b))),

                        // Ternary functions
                        "let" => op!(|a, b, c| match &*a {
                            Val::Sym(a) => {
                                let b = self.trans(&b);
                                self.env.push(a.clone());
                                let c = self.trans(&c);
                                self.env.pop();
                                Exp::let_(b, c)
                            }
                            _ => panic!("let binding name must be a symbol"),
                        }),
                        "lambda" => op!(|a, b, c| match (&*a, &*b) {
                            (Val::Sym(a), Val::Sym(b)) => {
                                self.env.push(a.clone());
                                self.env.push(b.clone());
                                let c = self.trans(&c);
                                self.env.pop();
                                self.env.pop();
                                Exp::lam(c)
                            }
                            _ => panic!("lambda self and parameter names must be symbols"),
                        }),
                        "if" => {
                            op!(|a, b, c| Exp::if_(self.trans(&a), self.trans(&b), self.trans(&c)))
                        }

                        _ => panic!("unrecognized function: {s}"),
                    },

                    _ => unpack_list!(2, |a, b| Exp::app(self.trans(&a), self.trans(&b))),
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
        let prog = "
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
        assert_eq!(parse(prog), Ok(parsed));
    }

    #[test]
    fn trans_example() {
        let prog = "
            (let code (lift (lambda f x (+ x 42)))
              code)
        ";
        let translated1 = Exp::let_(
            Exp::lift(Exp::lam(Exp::add(Exp::var(1), Exp::num(42)))),
            Exp::var(0),
        );
        let translated = trans(&parse(prog).unwrap(), VarEnv::new());
        assert_eq!(translated, translated1)
    }

    fn check_run(prog: &str, expected: Rc<Val>) {
        assert_eq!(ev(prog), expected);
    }

    fn check_code(prog: &str, expected: &str) {
        assert_eq!(ev(prog).unwrap_code().pretty(&Vec::new()), expected);
    }

    /// Tutorial from popl18/lisp.scala.
    #[test]
    fn tutorial() {
        // Some aspects of our multi-stage language may appear a bit
        // counterintuitive, but are essential for understanding how things work
        // -- especially how `lift` and `run` interact.

        // Broadly we can do two things very easily:
        // - Return code from the main program: `(lift ...)`
        // - Build code and run it: `(run 0 (.. (lift ..) ..))`

        // The key thing to avoid is calling `run` on code that is generated
        // outside of the `run` statement.

        // Below are some concrete examples.

        // (1)

        // Below, operator `lift` will `reflect` its argument, i.e., create a
        // new binding `Var(0) = Lam(Var(1))` in the current scope of
        // expressions being generated. The present-stage variable `code` will
        // be bound to expression `Code(Var(0))`. Whole-program evaluation
        // assembles all generated bindings into a nested let:
        check_run(
            "
            (let code (lift (lambda f x x))
              code)
            ",
            Val::code(Exp::let_(Exp::lam(Exp::var(1)), Exp::var(0))),
        );

        // Pretty-printing hides the let if the expression is of the form
        // `(let x e x)`.
        check_code(
            "
            (let code (lift (lambda f x x))
              code)
            ",
            "(lambda f0 x1 x1)",
        );

        // So the result of evaluating the whole expression is a block of code.
        // We can't ignore code that is reflected. For example,
        // `(let code (lift ..) 3)` would throw an exception.

        // (2)

        // Things may get surprising if we try to generate and run code at the
        // same time -- in general, one needs to avoid running code that is
        // generated outside of the `run` statement.

        // Intuitively we might expect the following code to return a plain
        // closure (create a lifted closure, then eval it to a value).

        check_run(
            "
            (let code (lift (lambda f x x))
              (run 0 code))
            ",
            Val::code(Exp::let_(Exp::lam(Exp::var(1)), Exp::var(0))),
        );

        // However, that's not what happens. Again, variable `code` is bound to
        // `Code(Var(0))`, the symbol generated from reflecting the
        // `(lift (lambda ...))`. So `run` is called with `Code(Var(0))`, i.e.,
        // `Var(0)` is the expression being evaluated, and that happens to be
        // exactly variable `code`, which is again mapped to `Code(Var(0))`.
        // Hence, the same result as in (1).

        // Let's test our understanding further:

        check_run(
            "
            (let z (lift 42)
              (let code (lift (lambda f x x))
                (run 0 code)))
            ",
            Val::code(Exp::let_(Exp::lam(Exp::var(1)), Exp::num(42))),
        );

        // Yes, this one returns 42, wrapped in a let that declares the lambda.

        // (Again, we have to use lift 42 instead of just 42, since we have to
        // return a code value.)

        // Future versions may entirely prohibit such uses, at the expense of
        // additional checks that associate a particular run-scope (or the top
        // level) with each Code value, and prevent mixing of levels.

        // (3)

        // Now how do we actually achieve the desired behavior: declare a
        // (closed) piece of code, then evaluate it?

        // Simple, we just wrap it in a function:

        check_run(
            "
            (let code (lambda _ _ (lift (lambda f x x)))
              (run 0 (code 'dummy)))
            ",
            Val::clo(
                Env::from_iter([Val::clo(Env::new(), Exp::lift(Exp::lam(Exp::var(3))))]),
                Exp::var(2),
            ),
        );

        // Disregarding the embedded closure environment that includes the value
        // of `code`, the result can be read more conveniently as
        // `Clo(code/Var0=..., (lambda f/Var1 x/Var2. x/Var))`.

        // The key is to ensure that all code pieces are reflected within the
        // **dynamic** scope of evaluating `run`'s argument, including functions
        // called within that dynamic extent.

        // (4)

        // What if we want to run the same code multiple times instead
        // re-generating it? Simple, generate a function and call it multiple
        // times.

        // (simple exercise -- note that we're already generating functions)

        // (5)

        // Note that generated code can refer to present-stage variables, using
        // `quote` and `trans`.

        // This has a similar effect to standard quotation, and comes with
        // similar hygiene issues (some are aggravated by our use of De Bruijn
        // levels for variable names).

        check_run(
            "
            (let z 21
              (let code (trans '(+ z z))
                (run 0 code)))
            ",
            Val::num(42),
        );

        // In contrast to `lift`, `trans` creates a closed code value directly.

        // Observe how the piece of code refers to variable `z = Var(0)`
        // directly:

        check_run(
            "
            (let z 21
              (let code (trans '(+ z z))
                code))
            ",
            Val::code(Exp::add(Exp::var(0), Exp::var(0))),
        );

        // Now let's take a look at the interaction with bindings inside a
        // `trans` block:

        check_run(
            "
            (let z 21
              (let code (trans '(lambda _ x (+ z x)))
                code))
            ",
            Val::code(Exp::lam(Exp::add(Exp::var(0), Exp::var(2)))),
        );

        // When we try to run this code, there's again a problem:

        check_run(
            "
            (let z 20
              (let code (trans '(lambda _ x (+ z x)))
                (let var2 10
                  (let f (run 0 code)
                    (f 22)))))
            ",
            Val::num(30),
        );

        // Intuitively we'd expect to get result 42, but we obtain 30. This
        // happens because `x` inside the `trans`ed lambda is `Var(2)` at this
        // position, but when `run` is called, `Var(2)` actually corresponds to
        // `var2`.

        // A more elaborate representation of bound and free names would fix
        // this (e.g., locally nameless) at the expense of complexity and
        // runtime overhead. Other hygiene issues (e.g., variables going out of
        // scope) would remain.

        // Right now, the recommendation is to use `trans` only as a direct
        // argument to `run`:

        check_run(
            "
            (let z 20
              (let var2 10
                (let f (run 0 (trans '(lambda _ x (+ z x))))
                  (f 22))))
            ",
            Val::num(42),
        );

        // This is good enough for the key use case of `trans` in `EM` (see
        // popl18/pink.scala).
    }
}

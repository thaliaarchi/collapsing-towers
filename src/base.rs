use std::collections::HashMap;
use std::fmt::{self, Display, Formatter};
use std::mem;
use std::rc::Rc;

use im_rc::Vector;

use crate::lisp::trans;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Exp {
    Num(i64),
    Sym(String),
    Var(usize),
    App(Rc<Exp>, Rc<Exp>),
    Lam(Rc<Exp>),
    Let(Rc<Exp>, Rc<Exp>),
    If(Rc<Exp>, Rc<Exp>, Rc<Exp>),
    Op1(Op1, Rc<Exp>),
    Op2(Op2, Rc<Exp>, Rc<Exp>),
    Cons(Rc<Exp>, Rc<Exp>),
    Lift(Rc<Exp>),
    Run(Rc<Exp>, Rc<Exp>),

    // Additional variant not in the paper, which operates on `Exp`. Implemented
    // in Scala as a regular variant.
    Log(Rc<Exp>, Rc<Exp>),
    // Additional variants not in the paper, which operate on `Val`. Implemented
    // in Scala with a lambda in `Special`.
    Quote(Rc<Val>),
    Trans(Rc<Val>, VarEnv),
    LiftRef(Rc<Val>, VarEnv),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Op1 {
    Car,
    Cdr,
    IsNum,
    IsSym,
    IsPair,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Op2 {
    Add,
    Sub,
    Mul,
    Eq,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Val {
    Num(i64),
    Sym(String),
    Pair(Rc<Val>, Rc<Val>),
    Clo(Env, Rc<Exp>),
    Code(Rc<Exp>),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Env {
    env: Vector<Rc<Val>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct VarEnv {
    env: Vec<String>,
}

#[derive(Clone, Debug)]
pub struct Vm {
    fresh: usize,
    block: Vec<Rc<Exp>>,
    fun: HashMap<(Env, Rc<Exp>), usize>,
}

impl Vm {
    pub fn new() -> Self {
        Vm {
            fresh: 0,
            block: Vec::new(),
            fun: HashMap::new(),
        }
    }

    fn run<T>(&mut self, f: impl FnOnce(&mut Vm) -> T) -> T {
        let fresh = self.fresh;
        let block = self.block.clone();
        let fun = self.fun.clone();
        let v = f(self);
        self.fresh = fresh;
        self.block = block;
        self.fun = fun;
        v
    }

    fn fresh(&mut self) -> Rc<Exp> {
        self.fresh += 1;
        Exp::var(self.fresh - 1)
    }

    fn reify(&mut self, f: impl FnOnce(&mut Self) -> Rc<Exp>) -> Rc<Exp> {
        let fresh = self.fresh;
        let mut block = Vec::new();
        mem::swap(&mut block, &mut self.block);
        let fun = self.fun.clone();
        let mut l = f(self);
        for e in self.block.drain(..).rev() {
            l = Exp::let_(e, l);
        }
        self.fresh = fresh;
        self.block = block;
        self.fun = fun;
        l
    }

    fn reflect(&mut self, s: Rc<Exp>) -> Rc<Exp> {
        self.block.push(s);
        self.fresh()
    }

    /// A-normal form conversion. Useful for checking generated against expected
    /// code.
    pub fn anf(&mut self, env: &Vector<Rc<Exp>>, e: &Rc<Exp>) -> Rc<Exp> {
        match &**e {
            Exp::Num(n) => Exp::num(*n),
            Exp::Sym(s) => Exp::sym(s.clone()),
            Exp::Var(x) => env[*x].clone(),
            Exp::App(e1, e2) => {
                let e1 = self.anf(env, e1);
                let e2 = self.anf(env, e2);
                self.reflect(Exp::app(e1, e2))
            }
            Exp::Lam(e) => {
                let e = self.reify(|vm| {
                    let mut env = env.clone();
                    env.push_back(vm.fresh());
                    env.push_back(vm.fresh());
                    vm.anf(&env, e)
                });
                self.reflect(Exp::lam(e))
            }
            Exp::Let(e1, e2) => {
                let e1 = self.anf(env, e1);
                let mut env = env.clone();
                env.push_back(e1);
                self.anf(&env, e2)
            }
            Exp::If(c, a, b) => {
                let c = self.anf(env, c);
                let a = self.reify(|vm| vm.anf(env, a));
                let b = self.reify(|vm| vm.anf(env, b));
                self.reflect(Exp::if_(c, a, b))
            }
            Exp::Op1(op, e) => {
                let e = self.anf(env, e);
                self.reflect(Exp::op1(*op, e))
            }
            Exp::Op2(op, e1, e2) => {
                let e1 = self.anf(env, e1);
                let e2 = self.anf(env, e2);
                self.reflect(Exp::op2(*op, e1, e2))
            }
            Exp::Cons(e1, e2) => {
                let e1 = self.anf(env, e1);
                let e2 = self.anf(env, e2);
                self.reflect(Exp::cons(e1, e2))
            }
            Exp::Lift(e) => {
                let e = self.anf(env, e);
                self.reflect(Exp::lift(e))
            }
            Exp::Run(b, e) => {
                let b = self.anf(env, b);
                let e = self.reify(|vm| vm.anf(env, e));
                self.reflect(Exp::run(b, e))
            }
            Exp::Log(b, e) => {
                let e = self.reify(|vm| vm.anf(env, e));
                self.reflect(Exp::log(b.clone(), e))
            }
            Exp::Quote(_) | Exp::Trans(_, _) | Exp::LiftRef(_, _) => self.reflect(e.clone()),
        }
    }

    fn reifyc(&mut self, f: impl FnOnce(&mut Vm) -> Rc<Val>) -> Rc<Exp> {
        self.reify(|vm| f(vm).unwrap_code())
    }
    fn reflectc(&mut self, s: Rc<Exp>) -> Rc<Val> {
        Val::code(self.reflect(s))
    }

    fn reifyv(&mut self, f: impl FnOnce(&mut Vm) -> Rc<Val>) -> Rc<Val> {
        self.run(|vm| {
            vm.block = Vec::new();
            let res = f(vm);
            if !vm.block.is_empty() {
                let mut l = res.unwrap_code();
                for e in vm.block.drain(..).rev() {
                    l = Exp::let_(e, l);
                }
                Val::code(l)
            } else {
                res
            }
        })
    }

    /// Normalization by Evaluation–style polymorphic lift operator.
    fn lift(&mut self, v: &Val) -> Rc<Exp> {
        match v {
            Val::Num(n) => Exp::num(*n),
            Val::Sym(s) => Exp::sym(s.clone()),
            Val::Pair(a, b) => self.reflect(Exp::cons(a.unwrap_code(), b.unwrap_code())),
            Val::Clo(env2, e2) => {
                let key = (env2.clone(), e2.clone());
                if let Some(var) = self.fun.get(&key) {
                    // Use the memoized computation. This is not essential to
                    // the algorithm, but appears necessary with recursion depth
                    // constraints.
                    Exp::var(*var)
                } else {
                    self.fun.insert(key, self.fresh);
                    let e = self.reify(|vm| {
                        let mut env = env2.clone();
                        env.push(Val::code(vm.fresh()));
                        env.push(Val::code(vm.fresh()));
                        vm.evalms(&env, &*e2).unwrap_code()
                    });
                    self.reflect(Exp::lam(e))
                }
            }
            Val::Code(e) => self.reflect(Exp::lift(e.clone())),
        }
    }

    /// Multi-stage evaluation.
    pub fn evalms(&mut self, env: &Env, e: &Exp) -> Rc<Val> {
        match e {
            Exp::Num(n) => Val::num(*n),
            Exp::Sym(s) => Val::sym(s.clone()),
            Exp::Var(x) => env.get(*x).unwrap(),
            Exp::Lam(e) => Val::clo(env.clone(), e.clone()),
            Exp::Let(e1, e2) => {
                let mut env2 = env.clone();
                env2.push(self.evalms(env, e1));
                self.evalms(&env2, e2)
            }

            Exp::Lift(e) => {
                let v = self.evalms(env, e);
                Val::code(self.lift(&*v))
            }

            Exp::Run(b, e) => match &*self.evalms(env, b) {
                // The first argument determines whether to generate `run`
                // statement or run code directly.
                Val::Code(b) => {
                    let e = self.reifyc(|vm| vm.evalms(env, e));
                    self.reflectc(Exp::run(b.clone(), e))
                }
                _ => {
                    let code = self.reifyc(|vm| {
                        vm.fresh = env.len();
                        vm.evalms(env, e)
                    });
                    self.reifyv(|vm| vm.evalms(env, &*code))
                }
            },

            Exp::Log(b, e) => match &*self.evalms(env, b) {
                Val::Code(b) => {
                    let e = self.reifyc(|vm| vm.evalms(env, e));
                    self.reflectc(Exp::log(b.clone(), e))
                }
                _ => {
                    let v = self.evalms(env, e);
                    println!("{v:?}");
                    v
                }
            },

            Exp::App(e1, e2) => {
                let v1 = self.evalms(env, e1);
                let v2 = self.evalms(env, e2);
                match (&*v1, &*v2) {
                    (Val::Clo(env3, e3), _) => {
                        let mut env = env3.clone();
                        env.push(Val::clo(env3.clone(), e3.clone()));
                        env.push(v2);
                        self.evalms(&env, &**e3)
                    }
                    (Val::Code(s1), Val::Code(s2)) => {
                        Val::code(self.reflect(Exp::app(s1.clone(), s2.clone())))
                    }
                    (v1, v2) => {
                        panic!("invalid app: {v1:?} {v2:?}");
                    }
                }
            }

            Exp::If(c, a, b) => match &*self.evalms(env, c) {
                Val::Num(0) => self.evalms(env, b),
                Val::Num(_) => self.evalms(env, a),
                Val::Code(c1) => {
                    let a = self.reifyc(|vm| vm.evalms(env, a));
                    let b = self.reifyc(|vm| vm.evalms(env, b));
                    self.reflectc(Exp::if_(c1.clone(), a, b))
                }
                c => panic!("invalid if: {c:?}"),
            },

            Exp::Op1(op, e) => {
                let v = self.evalms(env, e);
                match (*op, &*v) {
                    (op, Val::Code(s)) => Val::code(self.reflect(Exp::op1(op, s.clone()))),
                    (Op1::Car, Val::Pair(a, _)) => a.clone(),
                    (Op1::Cdr, Val::Pair(_, b)) => b.clone(),
                    (Op1::IsNum, v) => Val::bool(matches!(v, Val::Num(_))),
                    (Op1::IsSym, v) => Val::bool(matches!(v, Val::Sym(_))),
                    (Op1::IsPair, v) => Val::bool(matches!(v, Val::Pair(_, _))),
                    (op, v) => panic!("cannot eval ({op} {v:?})"),
                }
            }
            Exp::Op2(op, e1, e2) => {
                let v1 = self.evalms(env, e1);
                let v2 = self.evalms(env, e2);
                match (*op, &*v1, &*v2) {
                    (op, Val::Code(s1), Val::Code(s2)) => {
                        self.reflectc(Exp::op2(op, s1.clone(), s2.clone()))
                    }
                    (Op2::Add, Val::Num(n1), Val::Num(n2)) => Val::num(n1 + n2),
                    (Op2::Sub, Val::Num(n1), Val::Num(n2)) => Val::num(n1 - n2),
                    (Op2::Mul, Val::Num(n1), Val::Num(n2)) => Val::num(n1 * n2),
                    (Op2::Eq, v1, v2) => Val::bool(v1 == v2),
                    (op, v1, v2) => panic!("cannot eval ({op} {v1:?} {v2:?})"),
                }
            }
            Exp::Cons(e1, e2) => {
                let v1 = self.evalms(env, e1);
                let v2 = self.evalms(env, e2);
                Val::pair(v1, v2)
            }

            Exp::Quote(v) => v.clone(),
            Exp::Trans(v, venv) => {
                let v = self.evalms(env, &trans(v, venv.clone()));
                Val::code(trans(&v, venv.clone()))
            }
            Exp::LiftRef(v, venv) => {
                let v = self.evalms(env, &trans(v, venv.clone()));
                Val::code(Exp::quote(v))
            }
        }
    }
}

impl Exp {
    pub fn num(n: i64) -> Rc<Self> {
        Rc::new(Exp::Num(n))
    }
    pub fn sym(s: String) -> Rc<Self> {
        if s.contains(char::is_whitespace) {
            panic!("symbol contains whitespace");
        }
        Rc::new(Exp::Sym(s))
    }
    pub fn var(x: usize) -> Rc<Self> {
        Rc::new(Exp::Var(x))
    }
    pub fn app(e1: Rc<Exp>, e2: Rc<Exp>) -> Rc<Self> {
        Rc::new(Exp::App(e1, e2))
    }
    pub fn lam(e: Rc<Exp>) -> Rc<Self> {
        Rc::new(Exp::Lam(e))
    }
    pub fn let_(e1: Rc<Exp>, e2: Rc<Exp>) -> Rc<Self> {
        Rc::new(Exp::Let(e1, e2))
    }
    pub fn if_(b: Rc<Exp>, e1: Rc<Exp>, e2: Rc<Exp>) -> Rc<Self> {
        Rc::new(Exp::If(b, e1, e2))
    }
    pub fn op1(op: Op1, e: Rc<Exp>) -> Rc<Self> {
        Rc::new(Exp::Op1(op, e))
    }
    pub fn op2(op: Op2, e1: Rc<Exp>, e2: Rc<Exp>) -> Rc<Self> {
        Rc::new(Exp::Op2(op, e1, e2))
    }
    pub fn cons(e1: Rc<Exp>, e2: Rc<Exp>) -> Rc<Self> {
        Rc::new(Exp::Cons(e1, e2))
    }
    pub fn lift(e: Rc<Exp>) -> Rc<Self> {
        Rc::new(Exp::Lift(e))
    }
    pub fn run(b: Rc<Exp>, e: Rc<Exp>) -> Rc<Self> {
        Rc::new(Exp::Run(b, e))
    }
    pub fn log(b: Rc<Exp>, e: Rc<Exp>) -> Rc<Self> {
        Rc::new(Exp::Log(b, e))
    }
    pub fn quote(v: Rc<Val>) -> Rc<Self> {
        Rc::new(Exp::Quote(v))
    }
    pub fn trans(v: Rc<Val>, venv: VarEnv) -> Rc<Self> {
        Rc::new(Exp::Trans(v, venv))
    }
    pub fn lift_ref(v: Rc<Val>, venv: VarEnv) -> Rc<Self> {
        Rc::new(Exp::LiftRef(v, venv))
    }

    pub fn car(e: Rc<Exp>) -> Rc<Self> {
        Exp::op1(Op1::Car, e)
    }
    pub fn cdr(e: Rc<Exp>) -> Rc<Self> {
        Exp::op1(Op1::Cdr, e)
    }
    pub fn is_num(e: Rc<Exp>) -> Rc<Self> {
        Exp::op1(Op1::IsNum, e)
    }
    pub fn is_sym(e: Rc<Exp>) -> Rc<Self> {
        Exp::op1(Op1::IsSym, e)
    }
    pub fn is_pair(e: Rc<Exp>) -> Rc<Self> {
        Exp::op1(Op1::IsPair, e)
    }
    pub fn add(e1: Rc<Exp>, e2: Rc<Exp>) -> Rc<Self> {
        Exp::op2(Op2::Add, e1, e2)
    }
    pub fn sub(e1: Rc<Exp>, e2: Rc<Exp>) -> Rc<Self> {
        Exp::op2(Op2::Sub, e1, e2)
    }
    pub fn mul(e1: Rc<Exp>, e2: Rc<Exp>) -> Rc<Self> {
        Exp::op2(Op2::Mul, e1, e2)
    }
    pub fn eq(e1: Rc<Exp>, e2: Rc<Exp>) -> Rc<Self> {
        Exp::op2(Op2::Eq, e1, e2)
    }

    pub fn pretty(&self, env: &Vec<String>) -> String {
        match self {
            Exp::Num(n) => format!("{n}"),
            Exp::Sym(s) => format!("'{s}"),
            Exp::Var(x) => match env.get(*x) {
                Some(s) => s.clone(),
                None => "?".to_owned(),
            },
            Exp::Op1(op, a) => format!("({op} {})", a.pretty(env)),
            Exp::Op2(op, a, b) => format!("({op} {} {})", a.pretty(env), b.pretty(env)),
            Exp::Lift(a) => format!("(lift {})", a.pretty(env)),
            Exp::Cons(a, b) => format!("(cons {} {})", a.pretty(env), b.pretty(env)),
            Exp::Run(a, b) => format!("(run {} {})", a.pretty(env), b.pretty(env)),
            Exp::Log(a, b) => format!("(log {} {})", a.pretty(env), b.pretty(env)),
            Exp::App(a, b) => {
                format!("({} {})", a.pretty(env), b.pretty(env))
            }
            Exp::Let(a, b) => {
                let mut env2 = env.clone();
                env2.push(format!("x{}", env.len()));
                format!("(let x{} {} {})", env.len(), a.pretty(env), b.pretty(&env2))
            }
            Exp::Lam(e) => {
                let mut env2 = env.clone();
                env2.push(format!("f{}", env.len()));
                env2.push(format!("x{}", env.len() + 1));
                format!(
                    "(lambda f{} x{} {})",
                    env.len(),
                    env.len() + 1,
                    e.pretty(&env2),
                )
            }
            Exp::If(c, a, b) => {
                format!("(if {} {} {})", c.pretty(env), a.pretty(env), b.pretty(env))
            }
            Exp::Quote(v) => format!("'{}", v.pretty(env)),
            Exp::Trans(v, venv) => format!("(trans {} {})", v.pretty(env), venv.pretty()),
            Exp::LiftRef(v, venv) => format!("(lift-ref {} {})", v.pretty(env), venv.pretty()),
        }
    }
}

impl Val {
    pub fn num(n: i64) -> Rc<Self> {
        Rc::new(Val::Num(n))
    }
    pub fn sym<S: Into<String>>(s: S) -> Rc<Self> {
        Rc::new(Val::Sym(s.into()))
    }
    pub fn pair(a: Rc<Val>, b: Rc<Val>) -> Rc<Self> {
        Rc::new(Val::Pair(a, b))
    }
    pub fn clo(env: Env, e: Rc<Exp>) -> Rc<Self> {
        Rc::new(Val::Clo(env, e))
    }
    pub fn code(e: Rc<Exp>) -> Rc<Self> {
        Rc::new(Val::Code(e))
    }

    pub fn bool(b: bool) -> Rc<Self> {
        Val::num(if b { 1 } else { 0 })
    }

    fn unwrap_code(&self) -> Rc<Exp> {
        if let Val::Code(e) = self {
            e.clone()
        } else {
            panic!("val not code: {self:?}");
        }
    }

    pub fn pretty(&self, env: &Vec<String>) -> String {
        match self {
            Val::Num(n) => format!("{n}"),
            Val::Sym(s) => format!("{s}"),
            Val::Pair(a, b) => format!("({} {})", a.pretty(env), b.pretty(env)),
            Val::Clo(cenv, e) => format!("(closure {} {})", cenv.pretty(env), e.pretty(env)),
            Val::Code(e) => format!("(code {})", e.pretty(env)),
        }
    }
}

impl Env {
    pub fn new() -> Self {
        Env { env: Vector::new() }
    }

    pub fn get(&self, i: usize) -> Option<Rc<Val>> {
        self.env.get(i).map(Rc::clone)
    }

    pub fn push(&mut self, value: Rc<Val>) {
        self.env.push_back(value);
    }

    pub fn len(&self) -> usize {
        self.env.len()
    }

    pub fn pretty(&self, env: &Vec<String>) -> String {
        let mut s = String::new();
        s.push_str("(env");
        for v in &self.env {
            s.push(' ');
            s.push_str(&v.pretty(env));
        }
        s.push(')');
        s
    }
}

impl VarEnv {
    pub fn new() -> Self {
        VarEnv { env: Vec::new() }
    }

    pub fn get(&self, x: &str) -> Option<usize> {
        self.env
            .iter()
            .enumerate()
            .rev()
            .find(|&(_, y)| y == x)
            .map(|(i, _)| i)
    }

    pub fn push(&mut self, x: String) {
        self.env.push(x);
    }

    pub fn pop(&mut self) {
        self.env.pop().unwrap();
    }

    pub fn len(&self) -> usize {
        self.env.len()
    }

    pub fn pretty(&self) -> String {
        let mut s = String::new();
        s.push_str("(env");
        for v in &self.env {
            s.push(' ');
            s.push_str(v);
        }
        s.push(')');
        s
    }
}

impl Display for Op1 {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Op1::Car => write!(f, "car"),
            Op1::Cdr => write!(f, "cdr"),
            Op1::IsNum => write!(f, "num?"),
            Op1::IsSym => write!(f, "sym?"),
            Op1::IsPair => write!(f, "pair?"),
        }
    }
}

impl Display for Op2 {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Op2::Add => write!(f, "+"),
            Op2::Sub => write!(f, "-"),
            Op2::Mul => write!(f, "*"),
            Op2::Eq => write!(f, "eq?"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn factorial() {
        let f_self = Exp::app(Exp::var(0), Exp::num(99));
        let n = Exp::var(3);

        let fac_body = Exp::lam(Exp::if_(
            n.clone(),
            Exp::mul(
                n.clone(),
                Exp::app(f_self, Exp::sub(n, Exp::lift(Exp::num(1)))),
            ),
            Exp::lift(Exp::num(1)),
        ));
        let fac = Exp::app(Exp::lam(Exp::lift(fac_body)), Exp::num(99));
        let mut vm = Vm::new();
        let code = vm.reifyc(|vm| vm.evalms(&Env::new(), &*fac));
        let out = Exp::let_(
            Exp::lam(Exp::let_(
                Exp::if_(
                    Exp::var(1),
                    Exp::let_(
                        Exp::sub(Exp::var(1), Exp::num(1)),
                        Exp::let_(
                            Exp::app(Exp::var(0), Exp::var(2)),
                            Exp::let_(Exp::mul(Exp::var(1), Exp::var(3)), Exp::var(4)),
                        ),
                    ),
                    Exp::num(1),
                ),
                Exp::var(2),
            )),
            Exp::var(0),
        );
        assert_eq!(code, out);

        assert_eq!(
            Val::num(24),
            vm.evalms(&Env::new(), &Exp::App(code, Exp::num(4))),
        );
    }

    #[test]
    fn tree_sum() {
        let tree_sum = Exp::app(
            Exp::lam(/*0 1*/ Exp::app(
                Exp::lam(/*2 3*/ Exp::app(Exp::var(3), Exp::var(3))),
                Exp::lam(/*2 3*/ Exp::lam(/*4 5*/ Exp::lam(/*6 7*/ Exp::app(
                    Exp::app(
                        Exp::var(1),
                        Exp::app(
                            Exp::var(5),
                            Exp::app(Exp::app(Exp::var(3), Exp::var(3)), Exp::var(5)),
                        ),
                    ),
                    Exp::var(7),
                )))),
            )),
            Exp::lam(/*0 1*/ Exp::lam(/*2 3*/ Exp::if_(
                Exp::is_pair(Exp::var(3)),
                Exp::add(
                    Exp::app(Exp::var(1), Exp::car(Exp::var(3))),
                    Exp::app(Exp::var(1), Exp::cdr(Exp::var(3))),
                ),
                Exp::var(3),
            ))),
        );

        // Testing normal execution
        let mut vm = Vm::new();
        let v = vm.evalms(
            &Env::new(),
            &Exp::App(
                Exp::app(tree_sum.clone(), Exp::lam(Exp::var(1))),
                Exp::cons(Exp::cons(Exp::num(1), Exp::num(2)), Exp::num(3)),
            ),
        );
        assert_eq!(Val::num(6), v);

        let tree_sum_lifted = Exp::let_(
            /*0*/
            Exp::lam(/*0 1*/ Exp::let_(
                /*2*/ Exp::is_pair(Exp::var(1)),
                Exp::let_(
                    /*3*/
                    Exp::if_(
                        Exp::var(2),
                        Exp::let_(
                            /*3*/ Exp::car(Exp::var(1)),
                            Exp::let_(
                                /*4*/ Exp::app(Exp::var(0), Exp::var(3)),
                                Exp::let_(
                                    /*5*/ Exp::cdr(Exp::var(1)),
                                    Exp::let_(
                                        /*6*/ Exp::app(Exp::var(0), Exp::var(5)),
                                        Exp::let_(
                                            /*7*/ Exp::add(Exp::var(4), Exp::var(6)),
                                            Exp::var(7),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                        Exp::var(1),
                    ),
                    Exp::var(3),
                ),
            )),
            Exp::var(0),
        );

        // Testing lift
        let mut vm = Vm::new();
        let e = vm.reifyc(|vm| {
            vm.evalms(
                &Env::new(),
                &Exp::Lift(Exp::app(tree_sum.clone(), Exp::lam(Exp::lift(Exp::var(1))))),
            )
        });
        assert_eq!(tree_sum_lifted, e);
    }
}

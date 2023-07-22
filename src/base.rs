use std::collections::HashMap;
use std::mem;
use std::rc::Rc;

use im_rc::Vector;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Exp {
    Lit(i64),
    Sym(String),
    Var(usize),
    App(Rc<Exp>, Rc<Exp>),
    Lam(Rc<Exp>),
    Let(Rc<Exp>, Rc<Exp>),
    If(Rc<Exp>, Rc<Exp>, Rc<Exp>),
    Plus(Rc<Exp>, Rc<Exp>),
    Minus(Rc<Exp>, Rc<Exp>),
    Times(Rc<Exp>, Rc<Exp>),
    Equ(Rc<Exp>, Rc<Exp>),
    Cons(Rc<Exp>, Rc<Exp>),
    Fst(Rc<Exp>),
    Snd(Rc<Exp>),
    IsNum(Rc<Exp>),
    IsStr(Rc<Exp>),
    IsCons(Rc<Exp>),
    Lift(Rc<Exp>),
    Run(Rc<Exp>, Rc<Exp>),
    Log(Rc<Exp>, Rc<Exp>),
}

pub type Env = Vector<Rc<Val>>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Val {
    Cst(i64),
    Str(String),
    Tup(Rc<Val>, Rc<Val>),
    Clo(Env, Rc<Exp>),
    Code(Rc<Exp>),
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

    pub fn anf(&mut self, env: &Vector<Rc<Exp>>, e: &Exp) -> Rc<Exp> {
        macro_rules! anf1(($node:expr, $env:expr, $e:expr) => {{
            let e = self.anf($env, $e);
            self.reflect($node(e))
        }});
        macro_rules! anf2(($node:expr, $env:expr, $e1:expr, $e2:expr) => {{
            let e1 = self.anf($env, $e1);
            let e2 = self.anf($env, $e2);
            self.reflect($node(e1, e2))
        }});
        match e {
            Exp::Lit(n) => Exp::lit(*n),
            Exp::Sym(s) => Exp::sym(s.clone()),
            Exp::Var(x) => env[*x].clone(),
            Exp::App(e1, e2) => anf2!(Exp::app, env, e1, e2),
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
            Exp::Plus(e1, e2) => anf2!(Exp::plus, env, e1, e2),
            Exp::Minus(e1, e2) => anf2!(Exp::minus, env, e1, e2),
            Exp::Times(e1, e2) => anf2!(Exp::times, env, e1, e2),
            Exp::Equ(e1, e2) => anf2!(Exp::equ, env, e1, e2),
            Exp::Cons(e1, e2) => anf2!(Exp::cons, env, e1, e2),
            Exp::Fst(e) => anf1!(Exp::fst, env, e),
            Exp::Snd(e) => anf1!(Exp::snd, env, e),
            Exp::IsNum(e) => anf1!(Exp::is_num, env, e),
            Exp::IsStr(e) => anf1!(Exp::is_str, env, e),
            Exp::IsCons(e) => anf1!(Exp::is_cons, env, e),
            Exp::Lift(e) => anf1!(Exp::lift, env, e),
            Exp::Run(b, e) => {
                let b = self.anf(env, b);
                let e = self.reify(|vm| vm.anf(env, e));
                self.reflect(Exp::run(b, e))
            }
            Exp::Log(b, e) => {
                let e = self.reify(|vm| vm.anf(env, e));
                self.reflect(Exp::log(b.clone(), e))
            }
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

    fn lift(&mut self, v: &Val) -> Rc<Exp> {
        match v {
            Val::Cst(n) => Exp::lit(*n),
            Val::Str(s) => Exp::sym(s.clone()),
            Val::Tup(a, b) => self.reflect(Exp::cons(a.unwrap_code(), b.unwrap_code())),
            Val::Clo(env2, e2) => {
                let key = (env2.clone(), e2.clone());
                if let Some(var) = self.fun.get(&key) {
                    Exp::var(*var)
                } else {
                    self.fun.insert(key, self.fresh);
                    let e = self.reify(|vm| {
                        let mut env = env2.clone();
                        env.push_back(Val::code(vm.fresh()));
                        env.push_back(Val::code(vm.fresh()));
                        vm.evalms(&env, &*e2).unwrap_code()
                    });
                    self.reflect(Exp::lam(e))
                }
            }
            Val::Code(e) => self.reflect(Exp::lift(e.clone())),
        }
    }

    pub fn evalms(&mut self, env: &Env, e: &Exp) -> Rc<Val> {
        match e {
            Exp::Lit(n) => Val::cst(*n),
            Exp::Sym(s) => Val::str(s.clone()),
            Exp::Var(x) => env[*x].clone(),
            Exp::Lam(e) => Val::clo(env.clone(), e.clone()),
            Exp::Let(e1, e2) => {
                let mut env2 = env.clone();
                env2.push_back(self.evalms(env, e1));
                self.evalms(&env2, e2)
            }

            Exp::Lift(e) => {
                let v = self.evalms(env, e);
                Val::code(self.lift(&*v))
            }

            Exp::Run(b, e) => match &*self.evalms(env, b) {
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
                        env.push_back(Val::clo(env3.clone(), e3.clone()));
                        env.push_back(v2);
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
                Val::Cst(0) => self.evalms(env, b),
                Val::Cst(_) => self.evalms(env, a),
                Val::Code(c1) => {
                    let a = self.reifyc(|vm| vm.evalms(env, a));
                    let b = self.reifyc(|vm| vm.evalms(env, b));
                    self.reflectc(Exp::if_(c1.clone(), a, b))
                }
                c => panic!("invalid if: {c:?}"),
            },

            Exp::Plus(e1, e2) => {
                let v1 = self.evalms(env, e1);
                let v2 = self.evalms(env, e2);
                match (&*v1, &*v2) {
                    (Val::Cst(n1), Val::Cst(n2)) => Val::cst(n1 + n2),
                    (Val::Code(s1), Val::Code(s2)) => {
                        self.reflectc(Exp::plus(s1.clone(), s2.clone()))
                    }
                    (v1, v2) => panic!("invalid plus: {v1:?} + {v2:?}"),
                }
            }
            Exp::Minus(e1, e2) => {
                let v1 = self.evalms(env, e1);
                let v2 = self.evalms(env, e2);
                match (&*v1, &*v2) {
                    (Val::Cst(n1), Val::Cst(n2)) => Val::cst(n1 - n2),
                    (Val::Code(s1), Val::Code(s2)) => {
                        self.reflectc(Exp::minus(s1.clone(), s2.clone()))
                    }
                    (v1, v2) => panic!("invalid minus: {v1:?} - {v2:?}"),
                }
            }
            Exp::Times(e1, e2) => {
                let v1 = self.evalms(env, e1);
                let v2 = self.evalms(env, e2);
                match (&*v1, &*v2) {
                    (Val::Cst(n1), Val::Cst(n2)) => Val::cst(n1 * n2),
                    (Val::Code(s1), Val::Code(s2)) => {
                        self.reflectc(Exp::times(s1.clone(), s2.clone()))
                    }
                    (v1, v2) => panic!("invalid times: {v1:?} * {v2:?}"),
                }
            }
            Exp::Equ(e1, e2) => {
                let v1 = self.evalms(env, e1);
                let v2 = self.evalms(env, e2);
                match (&*v1, &*v2) {
                    (Val::Cst(n1), Val::Cst(n2)) => Val::bool(n1 == n2),
                    (Val::Str(s1), Val::Str(s2)) => Val::bool(s1 == s2),
                    (Val::Tup(a1, b1), Val::Tup(a2, b2)) => Val::bool(a1 == a2 && b1 == b2),
                    (Val::Code(s1), Val::Code(s2)) => {
                        self.reflectc(Exp::equ(s1.clone(), s2.clone()))
                    }
                    (v1, v2) => panic!("invalid equ: {v1:?} = {v2:?}"),
                }
            }
            Exp::Cons(e1, e2) => {
                let v1 = self.evalms(env, e1);
                let v2 = self.evalms(env, e2);
                Val::tup(v1, v2)
            }
            Exp::Fst(e1) => match &*self.evalms(env, e1) {
                Val::Tup(a, _) => a.clone(),
                Val::Code(s1) => Val::code(self.reflect(Exp::fst(s1.clone()))),
                v1 => panic!("invalid fst: {v1:?}"),
            },
            Exp::Snd(e1) => match &*self.evalms(env, e1) {
                Val::Tup(_, b) => b.clone(),
                Val::Code(s1) => Val::code(self.reflect(Exp::snd(s1.clone()))),
                v1 => panic!("invalid snd: {v1:?}"),
            },
            Exp::IsNum(e1) => match &*self.evalms(env, e1) {
                Val::Code(s1) => Val::code(self.reflect(Exp::is_num(s1.clone()))),
                v1 => Val::bool(matches!(v1, Val::Cst(_))),
            },
            Exp::IsStr(e1) => match &*self.evalms(env, e1) {
                Val::Code(s1) => Val::code(self.reflect(Exp::is_str(s1.clone()))),
                v1 => Val::bool(matches!(v1, Val::Str(_))),
            },
            Exp::IsCons(e1) => match &*self.evalms(env, e1) {
                Val::Code(s1) => Val::code(self.reflect(Exp::is_cons(s1.clone()))),
                v1 => Val::bool(matches!(v1, Val::Tup(_, _))),
            },
        }
    }
}

impl Exp {
    pub fn lit(n: i64) -> Rc<Self> {
        Rc::new(Exp::Lit(n))
    }
    pub fn sym(s: String) -> Rc<Self> {
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
    pub fn plus(e1: Rc<Exp>, e2: Rc<Exp>) -> Rc<Self> {
        Rc::new(Exp::Plus(e1, e2))
    }
    pub fn minus(e1: Rc<Exp>, e2: Rc<Exp>) -> Rc<Self> {
        Rc::new(Exp::Minus(e1, e2))
    }
    pub fn times(e1: Rc<Exp>, e2: Rc<Exp>) -> Rc<Self> {
        Rc::new(Exp::Times(e1, e2))
    }
    pub fn equ(e1: Rc<Exp>, e2: Rc<Exp>) -> Rc<Self> {
        Rc::new(Exp::Equ(e1, e2))
    }
    pub fn cons(e1: Rc<Exp>, e2: Rc<Exp>) -> Rc<Self> {
        Rc::new(Exp::Cons(e1, e2))
    }
    pub fn fst(e: Rc<Exp>) -> Rc<Self> {
        Rc::new(Exp::Fst(e))
    }
    pub fn snd(e: Rc<Exp>) -> Rc<Self> {
        Rc::new(Exp::Snd(e))
    }
    pub fn is_num(e: Rc<Exp>) -> Rc<Self> {
        Rc::new(Exp::IsNum(e))
    }
    pub fn is_str(e: Rc<Exp>) -> Rc<Self> {
        Rc::new(Exp::IsStr(e))
    }
    pub fn is_cons(e: Rc<Exp>) -> Rc<Self> {
        Rc::new(Exp::IsCons(e))
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

    pub fn pretty(&self, env: &Vec<String>) -> String {
        match self {
            Exp::Lit(n) => format!("{n}"),
            Exp::Sym(s) => format!("'{s}"),
            Exp::Var(x) => match env.get(*x) {
                Some(s) => s.clone(),
                None => "?".to_owned(),
            },
            Exp::IsNum(a) => format!("(num? {})", a.pretty(env)),
            Exp::IsStr(a) => format!("(str? {})", a.pretty(env)),
            Exp::IsCons(a) => format!("(tup? {})", a.pretty(env)),
            Exp::Lift(a) => format!("(lift {})", a.pretty(env)),
            Exp::Fst(a) => format!("(car {})", a.pretty(env)),
            Exp::Snd(a) => format!("(cdr {})", a.pretty(env)),
            Exp::Cons(a, b) => format!("(cons {} {})", a.pretty(env), b.pretty(env)),
            Exp::Equ(a, b) => format!("(eq? {} {})", a.pretty(env), b.pretty(env)),
            Exp::Plus(a, b) => format!("(+ {} {})", a.pretty(env), b.pretty(env)),
            Exp::Minus(a, b) => format!("(- {} {})", a.pretty(env), b.pretty(env)),
            Exp::Times(a, b) => format!("(* {} {})", a.pretty(env), b.pretty(env)),
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
        }
    }
}

impl Val {
    fn cst(n: i64) -> Rc<Self> {
        Rc::new(Val::Cst(n))
    }
    fn str(s: String) -> Rc<Self> {
        Rc::new(Val::Str(s))
    }
    fn tup(a: Rc<Val>, b: Rc<Val>) -> Rc<Self> {
        Rc::new(Val::Tup(a, b))
    }
    fn clo(env: Env, e: Rc<Exp>) -> Rc<Self> {
        Rc::new(Val::Clo(env, e))
    }
    fn code(e: Rc<Exp>) -> Rc<Self> {
        Rc::new(Val::Code(e))
    }

    fn bool(b: bool) -> Rc<Self> {
        Val::cst(if b { 1 } else { 0 })
    }

    fn unwrap_code(&self) -> Rc<Exp> {
        if let Val::Code(e) = self {
            e.clone()
        } else {
            panic!("val not code: {self:?}");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn factorial() {
        let f_self = Exp::app(Exp::var(0), Exp::lit(99));
        let n = Exp::var(3);

        let fac_body = Exp::lam(Exp::if_(
            n.clone(),
            Exp::times(
                n.clone(),
                Exp::app(f_self, Exp::minus(n, Exp::lift(Exp::lit(1)))),
            ),
            Exp::lift(Exp::lit(1)),
        ));
        let fac = Exp::app(Exp::lam(Exp::lift(fac_body)), Exp::lit(99));
        let mut vm = Vm::new();
        let code = vm.reifyc(|vm| vm.evalms(&Vector::new(), &*fac));
        let out = Exp::let_(
            Exp::lam(Exp::let_(
                Exp::if_(
                    Exp::var(1),
                    Exp::let_(
                        Exp::minus(Exp::var(1), Exp::lit(1)),
                        Exp::let_(
                            Exp::app(Exp::var(0), Exp::var(2)),
                            Exp::let_(Exp::times(Exp::var(1), Exp::var(3)), Exp::var(4)),
                        ),
                    ),
                    Exp::lit(1),
                ),
                Exp::var(2),
            )),
            Exp::var(0),
        );
        assert_eq!(code, out);

        assert_eq!(
            Val::cst(24),
            vm.evalms(&Vector::new(), &Exp::App(code, Exp::lit(4))),
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
                Exp::is_cons(Exp::var(3)),
                Exp::plus(
                    Exp::app(Exp::var(1), Exp::fst(Exp::var(3))),
                    Exp::app(Exp::var(1), Exp::snd(Exp::var(3))),
                ),
                Exp::var(3),
            ))),
        );

        // Testing normal execution
        let mut vm = Vm::new();
        let v = vm.evalms(
            &Vector::new(),
            &Exp::App(
                Exp::app(tree_sum.clone(), Exp::lam(Exp::var(1))),
                Exp::cons(Exp::cons(Exp::lit(1), Exp::lit(2)), Exp::lit(3)),
            ),
        );
        assert_eq!(Val::cst(6), v);

        let tree_sum_lifted = Exp::let_(
            /*0*/
            Exp::lam(/*0 1*/ Exp::let_(
                /*2*/ Exp::is_cons(Exp::var(1)),
                Exp::let_(
                    /*3*/
                    Exp::if_(
                        Exp::var(2),
                        Exp::let_(
                            /*3*/ Exp::fst(Exp::var(1)),
                            Exp::let_(
                                /*4*/ Exp::app(Exp::var(0), Exp::var(3)),
                                Exp::let_(
                                    /*5*/ Exp::snd(Exp::var(1)),
                                    Exp::let_(
                                        /*6*/ Exp::app(Exp::var(0), Exp::var(5)),
                                        Exp::let_(
                                            /*7*/ Exp::plus(Exp::var(4), Exp::var(6)),
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
                &Vector::new(),
                &Exp::Lift(Exp::app(tree_sum.clone(), Exp::lam(Exp::lift(Exp::var(1))))),
            )
        });
        assert_eq!(tree_sum_lifted, e);
    }
}

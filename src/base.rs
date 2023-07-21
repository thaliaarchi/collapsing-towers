use std::collections::HashMap;
use std::mem;

use im_rc::Vector;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Exp {
    Lit(i64),
    Sym(String),
    Var(usize),
    App(Box<Exp>, Box<Exp>),
    Lam(Box<Exp>),
    Let(Box<Exp>, Box<Exp>),
    If(Box<Exp>, Box<Exp>, Box<Exp>),
    Plus(Box<Exp>, Box<Exp>),
    Minus(Box<Exp>, Box<Exp>),
    Times(Box<Exp>, Box<Exp>),
    Equ(Box<Exp>, Box<Exp>),
    Cons(Box<Exp>, Box<Exp>),
    Fst(Box<Exp>),
    Snd(Box<Exp>),
    IsNum(Box<Exp>),
    IsStr(Box<Exp>),
    IsCons(Box<Exp>),
    Lift(Box<Exp>),
    Run(Box<Exp>, Box<Exp>),
    Log(Box<Exp>, Box<Exp>),
}

pub type Env = Vector<Val>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Val {
    Cst(i64),
    Str(String),
    Tup(Box<Val>, Box<Val>),
    Clo(Env, Box<Exp>),
    Code(Box<Exp>),
}

#[derive(Clone, Debug)]
pub struct Vm {
    fresh: usize,
    block: Vec<Exp>,
    fun: HashMap<(Env, Box<Exp>), usize>,
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

    fn fresh(&mut self) -> Exp {
        self.fresh += 1;
        Exp::Var(self.fresh - 1)
    }

    fn reify(&mut self, f: impl FnOnce(&mut Self) -> Box<Exp>) -> Box<Exp> {
        let fresh = self.fresh;
        let mut block = Vec::new();
        mem::swap(&mut block, &mut self.block);
        let fun = self.fun.clone();
        let mut l = f(self);
        for e in self.block.drain(..).rev() {
            l = Box::new(Exp::Let(Box::new(e), l));
        }
        self.fresh = fresh;
        self.block = block;
        self.fun = fun;
        l
    }

    fn reflect(&mut self, s: Exp) -> Box<Exp> {
        self.block.push(s);
        Box::new(self.fresh())
    }

    pub fn anf(&mut self, env: &Vector<Exp>, e: Box<Exp>) -> Box<Exp> {
        match *e {
            Exp::Lit(n) => Box::new(Exp::Lit(n)),
            Exp::Sym(s) => Box::new(Exp::Sym(s)),
            Exp::Var(n) => Box::new(env[n].clone()),
            Exp::App(e1, e2) => {
                let e1 = self.anf(env, e1);
                let e2 = self.anf(env, e2);
                self.reflect(Exp::App(e1, e2))
            }
            Exp::Lam(e) => {
                let e = self.reify(|vm| {
                    let mut env = env.clone();
                    env.push_back(vm.fresh());
                    env.push_back(vm.fresh());
                    vm.anf(&env, e)
                });
                self.reflect(Exp::Lam(e))
            }
            Exp::Let(e1, e2) => {
                let e1 = self.anf(env, e1);
                let mut env = env.clone();
                env.push_back(*e1);
                self.anf(&env, e2)
            }
            Exp::If(c, a, b) => {
                let c = self.anf(env, c);
                let a = self.reify(|vm| vm.anf(env, a));
                let b = self.reify(|vm| vm.anf(env, b));
                self.reflect(Exp::If(c, a, b))
            }
            Exp::Plus(e1, e2) => {
                let e1 = self.anf(env, e1);
                let e2 = self.anf(env, e2);
                self.reflect(Exp::Plus(e1, e2))
            }
            Exp::Minus(e1, e2) => {
                let e1 = self.anf(env, e1);
                let e2 = self.anf(env, e2);
                self.reflect(Exp::Minus(e1, e2))
            }
            Exp::Times(e1, e2) => {
                let e1 = self.anf(env, e1);
                let e2 = self.anf(env, e2);
                self.reflect(Exp::Times(e1, e2))
            }
            Exp::Equ(e1, e2) => {
                let e1 = self.anf(env, e1);
                let e2 = self.anf(env, e2);
                self.reflect(Exp::Equ(e1, e2))
            }
            Exp::Cons(e1, e2) => {
                let e1 = self.anf(env, e1);
                let e2 = self.anf(env, e2);
                self.reflect(Exp::Cons(e1, e2))
            }
            Exp::Fst(e) => {
                let e = self.anf(env, e);
                self.reflect(Exp::Fst(e))
            }
            Exp::Snd(e) => {
                let e = self.anf(env, e);
                self.reflect(Exp::Snd(e))
            }
            Exp::IsNum(e) => {
                let e = self.anf(env, e);
                self.reflect(Exp::IsNum(e))
            }
            Exp::IsStr(e) => {
                let e = self.anf(env, e);
                self.reflect(Exp::IsStr(e))
            }
            Exp::IsCons(e) => {
                let e = self.anf(env, e);
                self.reflect(Exp::IsCons(e))
            }
            Exp::Lift(e) => {
                let e = self.anf(env, e);
                self.reflect(Exp::Lift(e))
            }
            Exp::Run(b, e) => {
                let b = self.anf(env, b);
                let e = self.reify(|vm| vm.anf(env, e));
                self.reflect(Exp::Run(b, e))
            }
            Exp::Log(b, e) => {
                let e = self.reify(|vm| vm.anf(env, e));
                self.reflect(Exp::Log(b, e))
            }
        }
    }

    fn reifyc(&mut self, f: impl FnOnce(&mut Vm) -> Val) -> Box<Exp> {
        self.reify(|vm| f(vm).unwrap_code())
    }
    fn reflectc(&mut self, s: Exp) -> Val {
        Val::Code(self.reflect(s))
    }

    fn reifyv(&mut self, f: impl FnOnce(&mut Vm) -> Val) -> Val {
        self.run(|vm| {
            vm.block = Vec::new();
            let res = f(vm);
            if !vm.block.is_empty() {
                let mut l = res.unwrap_code();
                for e in vm.block.drain(..).rev() {
                    l = Box::new(Exp::Let(Box::new(e), l));
                }
                Val::Code(l)
            } else {
                res
            }
        })
    }

    fn lift(&mut self, v: Val) -> Box<Exp> {
        match v {
            Val::Cst(n) => Box::new(Exp::Lit(n)),
            Val::Str(s) => Box::new(Exp::Sym(s)),
            Val::Tup(a, b) => self.reflect(Exp::Cons(a.unwrap_code(), b.unwrap_code())),
            Val::Clo(env2, e2) => {
                let key = (env2.clone(), e2.clone());
                if let Some(var) = self.fun.get(&key) {
                    Box::new(Exp::Var(*var))
                } else {
                    self.fun.insert(key, self.fresh);
                    let e = self.reify(|vm| {
                        let mut env = env2.clone();
                        env.push_back(Val::Code(Box::new(vm.fresh())));
                        env.push_back(Val::Code(Box::new(vm.fresh())));
                        vm.evalms(&env, e2.clone()).unwrap_code()
                    });
                    self.reflect(Exp::Lam(e))
                }
            }
            Val::Code(e) => self.reflect(Exp::Lift(e)),
        }
    }

    pub fn evalms(&mut self, env: &Env, e: Box<Exp>) -> Val {
        match *e {
            Exp::Lit(n) => Val::Cst(n),
            Exp::Sym(s) => Val::Str(s),
            Exp::Var(n) => env[n].clone(),
            Exp::Lam(e) => Val::Clo(env.clone(), e),
            Exp::Let(e1, e2) => {
                let mut env2 = env.clone();
                env2.push_back(self.evalms(env, e1));
                self.evalms(&env2, e2)
            }

            Exp::Lift(e) => {
                let v = self.evalms(env, e);
                Val::Code(self.lift(v))
            }

            Exp::Run(b, e) => match self.evalms(env, b) {
                Val::Code(b) => {
                    let e = self.reifyc(|vm| vm.evalms(env, e));
                    self.reflectc(Exp::Run(b, e))
                }
                _ => {
                    let code = self.reifyc(|vm| {
                        vm.fresh = env.len();
                        vm.evalms(env, e)
                    });
                    self.reifyv(|vm| vm.evalms(env, code))
                }
            },

            Exp::Log(b, e) => match self.evalms(env, b) {
                Val::Code(b) => {
                    let e = self.reifyc(|vm| vm.evalms(env, e));
                    self.reflectc(Exp::Log(b, e))
                }
                _ => {
                    let v = self.evalms(env, e);
                    println!("{v:?}");
                    v
                }
            },

            Exp::App(e1, e2) => {
                let r1 = self.evalms(env, e1);
                let r2 = self.evalms(env, e2);
                match (r1, r2) {
                    (Val::Clo(mut env3, e3), v2) => {
                        env3.push_back(Val::Clo(env3.clone(), e3.clone()));
                        env3.push_back(v2);
                        self.evalms(&env3, e3)
                    }
                    (Val::Code(s1), Val::Code(s2)) => Val::Code(self.reflect(Exp::App(s1, s2))),
                    (r1, r2) => {
                        panic!("invalid app: {r1:?} {r2:?}");
                    }
                }
            }

            Exp::If(c, a, b) => match self.evalms(env, c) {
                Val::Cst(0) => self.evalms(env, b),
                Val::Cst(_) => self.evalms(env, a),
                Val::Code(c1) => {
                    let a = self.reifyc(|vm| vm.evalms(env, a));
                    let b = self.reifyc(|vm| vm.evalms(env, b));
                    self.reflectc(Exp::If(c1, a, b))
                }
                c => panic!("invalid if: {c:?}"),
            },

            Exp::Plus(e1, e2) => {
                let r1 = self.evalms(env, e1);
                let r2 = self.evalms(env, e2);
                match (r1, r2) {
                    (Val::Cst(n1), Val::Cst(n2)) => Val::Cst(n1 + n2),
                    (Val::Code(s1), Val::Code(s2)) => self.reflectc(Exp::Plus(s1, s2)),
                    (r1, r2) => panic!("invalid plus: {r1:?} + {r2:?}"),
                }
            }
            Exp::Minus(e1, e2) => {
                let r1 = self.evalms(env, e1);
                let r2 = self.evalms(env, e2);
                match (r1, r2) {
                    (Val::Cst(n1), Val::Cst(n2)) => Val::Cst(n1 - n2),
                    (Val::Code(s1), Val::Code(s2)) => self.reflectc(Exp::Minus(s1, s2)),
                    (r1, r2) => panic!("invalid minus: {r1:?} - {r2:?}"),
                }
            }
            Exp::Times(e1, e2) => {
                let r1 = self.evalms(env, e1);
                let r2 = self.evalms(env, e2);
                match (r1, r2) {
                    (Val::Cst(n1), Val::Cst(n2)) => Val::Cst(n1 * n2),
                    (Val::Code(s1), Val::Code(s2)) => self.reflectc(Exp::Times(s1, s2)),
                    (r1, r2) => panic!("invalid times: {r1:?} * {r2:?}"),
                }
            }
            Exp::Equ(e1, e2) => {
                let r1 = self.evalms(env, e1);
                let r2 = self.evalms(env, e2);
                match (r1, r2) {
                    (Val::Cst(n1), Val::Cst(n2)) => Val::bool(n1 == n2),
                    (Val::Str(s1), Val::Str(s2)) => Val::bool(s1 == s2),
                    (Val::Tup(a1, b1), Val::Tup(a2, b2)) => Val::bool(a1 == a2 && b1 == b2),
                    (Val::Code(s1), Val::Code(s2)) => self.reflectc(Exp::Equ(s1, s2)),
                    (r1, r2) => panic!("invalid equ: {r1:?} = {r2:?}"),
                }
            }
            Exp::Cons(e1, e2) => {
                let v1 = self.evalms(env, e1);
                let v2 = self.evalms(env, e2);
                Val::Tup(Box::new(v1), Box::new(v2))
            }
            Exp::Fst(e1) => match self.evalms(env, e1) {
                Val::Tup(a, _) => *a,
                Val::Code(s1) => Val::Code(self.reflect(Exp::Fst(s1))),
                r1 => panic!("invalid fst: {r1:?}"),
            },
            Exp::Snd(e1) => match self.evalms(env, e1) {
                Val::Tup(_, b) => *b,
                Val::Code(s1) => Val::Code(self.reflect(Exp::Snd(s1))),
                r1 => panic!("invalid snd: {r1:?}"),
            },
            Exp::IsNum(e1) => match self.evalms(env, e1) {
                Val::Code(s1) => Val::Code(self.reflect(Exp::IsNum(s1))),
                r1 => Val::bool(matches!(r1, Val::Cst(_))),
            },
            Exp::IsStr(e1) => match self.evalms(env, e1) {
                Val::Code(s1) => Val::Code(self.reflect(Exp::IsStr(s1))),
                r1 => Val::bool(matches!(r1, Val::Str(_))),
            },
            Exp::IsCons(e1) => match self.evalms(env, e1) {
                Val::Code(s1) => Val::Code(self.reflect(Exp::IsCons(s1))),
                r1 => Val::bool(matches!(r1, Val::Tup(_, _))),
            },
        }
    }
}

impl Exp {
    pub fn pretty(&self, env: &Vec<String>) -> String {
        match self {
            Exp::Lit(n) => format!("{n}"),
            Exp::Sym(n) => format!("'{n}"),
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
    fn unwrap_code(self) -> Box<Exp> {
        if let Val::Code(e) = self {
            e
        } else {
            panic!("val not code: {self:?}");
        }
    }

    fn bool(b: bool) -> Self {
        Val::Cst(if b { 1 } else { 0 })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn factorial() {
        let f_self = Box::new(Exp::App(Box::new(Exp::Var(0)), Box::new(Exp::Lit(99))));
        let n = Box::new(Exp::Var(3));

        let fac_body = Box::new(Exp::Lam(Box::new(Exp::If(
            n.clone(),
            Box::new(Exp::Times(
                n.clone(),
                Box::new(Exp::App(
                    f_self,
                    Box::new(Exp::Minus(n, Box::new(Exp::Lift(Box::new(Exp::Lit(1)))))),
                )),
            )),
            Box::new(Exp::Lift(Box::new(Exp::Lit(1)))),
        ))));
        let fac = Box::new(Exp::App(
            Box::new(Exp::Lam(Box::new(Exp::Lift(fac_body)))),
            Box::new(Exp::Lit(99)),
        ));
        let mut vm = Vm::new();
        let code = vm.reifyc(|vm| vm.evalms(&Vector::new(), fac));
        let out = Box::new(Exp::Let(
            Box::new(Exp::Lam(Box::new(Exp::Let(
                Box::new(Exp::If(
                    Box::new(Exp::Var(1)),
                    Box::new(Exp::Let(
                        Box::new(Exp::Minus(Box::new(Exp::Var(1)), Box::new(Exp::Lit(1)))),
                        Box::new(Exp::Let(
                            Box::new(Exp::App(Box::new(Exp::Var(0)), Box::new(Exp::Var(2)))),
                            Box::new(Exp::Let(
                                Box::new(Exp::Times(Box::new(Exp::Var(1)), Box::new(Exp::Var(3)))),
                                Box::new(Exp::Var(4)),
                            )),
                        )),
                    )),
                    Box::new(Exp::Lit(1)),
                )),
                Box::new(Exp::Var(2)),
            )))),
            Box::new(Exp::Var(0)),
        ));
        assert_eq!(code, out);

        assert_eq!(
            Val::Cst(24),
            vm.evalms(
                &Vector::new(),
                Box::new(Exp::App(code, Box::new(Exp::Lit(4))))
            ),
        );
    }

    #[test]
    fn tree_sum() {
        let tree_sum = Box::new(Exp::App(
            Box::new(Exp::Lam(/*0 1*/ Box::new(Exp::App(
                Box::new(Exp::Lam(/*2 3*/ Box::new(Exp::App(
                    Box::new(Exp::Var(3)),
                    Box::new(Exp::Var(3)),
                )))),
                Box::new(Exp::Lam(/*2 3*/ Box::new(Exp::Lam(
                    /*4 5*/
                    Box::new(Exp::Lam(/*6 7*/ Box::new(Exp::App(
                        Box::new(Exp::App(
                            Box::new(Exp::Var(1)),
                            Box::new(Exp::App(
                                Box::new(Exp::Var(5)),
                                Box::new(Exp::App(
                                    Box::new(Exp::App(
                                        Box::new(Exp::Var(3)),
                                        Box::new(Exp::Var(3)),
                                    )),
                                    Box::new(Exp::Var(5)),
                                )),
                            )),
                        )),
                        Box::new(Exp::Var(7)),
                    )))),
                )))),
            )))),
            Box::new(Exp::Lam(
                /*0 1*/
                Box::new(Exp::Lam(/*2 3*/ Box::new(Exp::If(
                    Box::new(Exp::IsCons(Box::new(Exp::Var(3)))),
                    Box::new(Exp::Plus(
                        Box::new(Exp::App(
                            Box::new(Exp::Var(1)),
                            Box::new(Exp::Fst(Box::new(Exp::Var(3)))),
                        )),
                        Box::new(Exp::App(
                            Box::new(Exp::Var(1)),
                            Box::new(Exp::Snd(Box::new(Exp::Var(3)))),
                        )),
                    )),
                    Box::new(Exp::Var(3)),
                )))),
            )),
        ));

        // Testing normal execution
        let mut vm = Vm::new();
        let v = vm.evalms(
            &Vector::new(),
            Box::new(Exp::App(
                Box::new(Exp::App(
                    tree_sum.clone(),
                    Box::new(Exp::Lam(Box::new(Exp::Var(1)))),
                )),
                Box::new(Exp::Cons(
                    Box::new(Exp::Cons(Box::new(Exp::Lit(1)), Box::new(Exp::Lit(2)))),
                    Box::new(Exp::Lit(3)),
                )),
            )),
        );
        assert_eq!(Val::Cst(6), v);

        let tree_sum_lifted = Box::new(Exp::Let(
            /*0*/
            Box::new(Exp::Lam(/*0 1*/ Box::new(Exp::Let(
                /*2*/ Box::new(Exp::IsCons(Box::new(Exp::Var(1)))),
                Box::new(Exp::Let(
                    /*3*/
                    Box::new(Exp::If(
                        Box::new(Exp::Var(2)),
                        Box::new(Exp::Let(
                            /*3*/ Box::new(Exp::Fst(Box::new(Exp::Var(1)))),
                            Box::new(Exp::Let(
                                /*4*/
                                Box::new(Exp::App(Box::new(Exp::Var(0)), Box::new(Exp::Var(3)))),
                                Box::new(Exp::Let(
                                    /*5*/ Box::new(Exp::Snd(Box::new(Exp::Var(1)))),
                                    Box::new(Exp::Let(
                                        /*6*/
                                        Box::new(Exp::App(
                                            Box::new(Exp::Var(0)),
                                            Box::new(Exp::Var(5)),
                                        )),
                                        Box::new(Exp::Let(
                                            /*7*/
                                            Box::new(Exp::Plus(
                                                Box::new(Exp::Var(4)),
                                                Box::new(Exp::Var(6)),
                                            )),
                                            Box::new(Exp::Var(7)),
                                        )),
                                    )),
                                )),
                            )),
                        )),
                        Box::new(Exp::Var(1)),
                    )),
                    Box::new(Exp::Var(3)),
                )),
            )))),
            Box::new(Exp::Var(0)),
        ));

        // Testing lift
        let mut vm = Vm::new();
        let e = vm.reifyc(|vm| {
            vm.evalms(
                &Vector::new(),
                Box::new(Exp::Lift(Box::new(Exp::App(
                    tree_sum.clone(),
                    Box::new(Exp::Lam(Box::new(Exp::Lift(Box::new(Exp::Var(1)))))),
                )))),
            )
        });
        assert_eq!(tree_sum_lifted, e);
    }
}

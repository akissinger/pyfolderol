from __future__ import annotations
from dataclasses import dataclass, field
from enum import Enum
from typing import Dict, List, Mapping, Set, Tuple, Optional
from functools import reduce

from lark import Lark, Transformer

class MatchError(Exception): pass
class UnifyError(Exception): pass


# TERMS AND FORMULAS

class Q(Enum):
    ALL = '∀'
    EX = '∃'

class C(Enum):
    AND = '∧'
    OR = '∨'
    NOT = '¬'
    IMPLIES = '⟶'
    IFF = '⟷'

class Term:
    def __str__(self) -> str: return self.rstr([])

    def rstr(self, _):
        return 'TERM'

    def vars(self, include_deps=False) -> Set[str]:
        match self:
            case Var(a): return set([a])
            case Param(a, ds): return ds if include_deps else set()
            case Fun(_, ts):
                return reduce(lambda vs,t: vs.union(t.vars()), ts, set())
            case _: return set()

    def var_occurs(self, v: str) -> bool:
        return v in self.vars(include_deps=True)

    def replace(self, u: Term, v: Term) -> Term:
        if self == u: return v
        match self:
            case Fun(a, ts): return Fun(a, [t.replace(u, v) for t in ts])
            case _: return self

@dataclass
class Var(Term):
    name: str
    def rstr(self, _): return '?' + self.name

@dataclass
class Param(Term):
    name: str
    deps: Set[str] = field(default_factory=lambda: set())
    def rstr(self, _): return self.name

@dataclass
class Bound(Term):
    i: int
    def rstr(self, bs): return bs[self.i]

@dataclass
class Fun(Term):
    name: str
    args: List[Term]

    def rstr(self, bs):
        if len(self.args) == 0: return self.name
        else: return self.name + '(' + ', '.join([a.rstr(bs) for a in self.args]) + ')'

class Form:
    def __str__(self) -> str:
        return self.rstr([])
    def __repr__(self) -> str:
        return self.rstr([])
    def rstr(self, _):
        return 'FORMULA'

    def vars(self) -> Set[str]:
        match self:
            case Pred(_,ts): return reduce(lambda vs, t: vs.union(t.vars()), ts, set())
            case Conn(_,As): return reduce(lambda vs, A: vs.union(A.vars()), As, set())
            case Quant(_,_,A): return A.vars()
            case _: raise MatchError

    def abstract(self, t: Term, depth: int=0) -> Form:
        match self:
            case Pred(a, us):
                return Pred(a, [u.replace(t, Bound(depth)) for u in us])
            case Conn(b, As):
                return Conn(b, [A.abstract(t, depth) for A in As])
            case Quant(q, b, A):
                return Quant(q, b, A.abstract(t, depth+1))
            case _: raise MatchError

    def subst_bound(self, t: Term, depth: int=0) -> Form:
        match self:
            case Pred(a, us):
                return Pred(a, [u.replace(Bound(depth), t) for u in us])
            case Conn(b, As):
                return Conn(b, [A.subst_bound(t, depth) for A in As])
            case Quant(q, b, A):
                return Quant(q, b, A.subst_bound(t, depth+1))
            case _: raise MatchError
            

@dataclass
class Pred(Form):
    name: str
    args: List[Term]

    def rstr(self, bs) -> str:
        if len(self.args) == 0: return self.name
        else: return self.name + '(' + ', '.join([a.rstr(bs) for a in self.args]) + ')'

@dataclass
class Conn(Form):
    c: C
    args: List[Form]

    def rstr(self, bs) -> str:
        if self.c == C.NOT:
            return self.c.value + '(' + self.args[0].rstr(bs) + ')'
        else:
            return '(' + (' ' + self.c.value + ' ').join([a.rstr(bs) for a in self.args]) + ')'

@dataclass
class Quant(Form):
    q: Q
    bname: str
    body: Form
    
    def __eq__(self, other):
        return self.q == other.q and self.body == other.body

    def rstr(self, bs) -> str:
        return self.q.value + self.bname + '.' + self.body.rstr([self.bname, *bs])

@dataclass
class Goal:
    left: List[Form]
    right: List[Form]
    def __str__(self) -> str:
        return (', '.join(map(str, self.left)) + ' ⊢ ' + 
                ', '.join(map(str, self.right)))
    def copy(self):
        return Goal(self.left.copy(), self.right.copy())

    def extend(self, left: List[Form], right: List[Form]) -> Goal:
        g = self.copy()
        g.left += left
        g.right += right
        return g

    def vars(self) -> Set[str]:
        return reduce(lambda vs, p: vs.union(p.vars()), self.left + self.right, set())


# PARSER

GRAMMAR = Lark("""
    goal      : formlist TURNSTILE formlist
    formlist  : [ form ("," form)* ]

    form      : quant | conn | pred | "(" form ")"
    quant     : ALL IDENT "." form | EX IDENT "." form
    conn      : NOT form | form AND form | form OR form | form IMPLIES form | form IFF form
    pred      : IDENT "(" term ("," term)* ")" | IDENT
    
    term      : var | fun
    var       : META
    fun       : IDENT "(" term ("," term)* ")" | IDENT
    
    TURNSTILE : "|-" | "⊢"
    ALL       : "forall" | "∀"
    EX        : "exists" | "∃"
    AND       : "and" | "∧"
    OR        : "or" | "∨"
    NOT       : "not" | "¬"
    IMPLIES   : "implies" | "->" | "⟶"
    IFF       : "iff" | "<->" | "⟷"

    IDENT  : ("_"|LETTER|DIGIT)+
    META   : "?" ("_"|LETTER|DIGIT)*
    %import common.LETTER
    %import common.DIGIT
    %import common.WS
    %ignore WS
""", start=["goal", "form", "term"])

class BuildGoal(Transformer):
    def goal(self, items): return Goal(items[0], items[2])
    def formlist(self, items):
        if isinstance(items, list): return items
        else: return [items]
    def form(self, items): return items[0]
    def quant(self, items):
        return Quant(items[0], items[1], items[2].abstract(Fun(items[1], [])))
    def conn(self, items):
        if len(items) == 2: return Conn(items[0], [items[1]])
        else: return Conn(items[1], [items[0], items[2]])
    def pred(self, items): return Pred(items[0], items[1:])
    def term(self, items): return items[0]
    def var(self, items): return Var(items[0])
    def fun(self, items): return Fun(items[0], items[1:])
    def ALL(self, _): return Q.ALL
    def EX(self, _): return Q.EX
    def AND(self, _): return C.AND
    def OR(self, _): return C.OR
    def NOT(self, _): return C.NOT
    def IMPLIES(self, _): return C.IMPLIES
    def IFF(self, _): return C.IFF
    def IDENT(self, item): return str(item)
    def META(self, item): return str(item)[1:]

def parse_goal(s: str) -> Goal:
    return BuildGoal().transform(GRAMMAR.parse(s, "goal"))

def parse_form(s: str) -> Form:
    return BuildGoal().transform(GRAMMAR.parse(s, "form"))

def parse_term(s: str) -> Term:
    return BuildGoal().transform(GRAMMAR.parse(s, "term"))


# UNIFICATION

Env = Mapping[str, Term]

def chase_var(t: Term, env: Env) -> Term:
    match t:
        case Var(a) if a in env: return chase_var(env[a], env)
    return t

def unify_terms(ts: List[Term], us: List[Term],
                env: Env) -> Env:
    if len(ts) != len(us):
        raise UnifyError
    elif len(ts) == 0:
        return env

    def unify_var(t: Term, u: Term):
        match t:
            case Var(a):
                if t == u: return env
                elif u.var_occurs(a): raise UnifyError
                else:
                    env1 = dict(**env)
                    env1[a] = u
                    return env1
            case _:
                return unify_term(t, u)

    def unify_term(t: Term, u: Term):
        match (t, u):
            case (Var(a), _):
                return unify_var(chase_var(Var(a), env), chase_var(u, env))
            case (_, Var(a)):
                return unify_var(chase_var(Var(a), env), chase_var(t, env))
            case (Param(a, _), Param(b, _)) if a == b:
                return env
            case (Fun(a, ts), Fun(b, us)) if a == b:
                return unify_terms(ts, us, env)
            case _:
                raise UnifyError

    return unify_terms(ts[1:], us[1:], unify_term(ts[0], us[0]))

def unify(p: Form, q: Form, env: Env) -> Env:
    match (p,q):
        case (Pred(a, ts), Pred(b, us)) if a == b: return unify_terms(ts, us, env)
    raise UnifyError

def inst_term(env: Env, t: Term) -> Term:
    match t:
        case Fun(a, us):
            return Fun(a, [inst_term(env, u) for u in us])
        case Param(a, bs):
            return Param(a, reduce(lambda vs, t: vs.union(t.vars()),
                                   [inst_term(env, Var(b)) for b in bs],
                                   set()))
        case Var(a) if a in env:
            return inst_term(env, env[a])
    return t

def inst_form(env: Env, form: Form) -> Form:
    match form:
        case Pred(a, ts): return Pred(a, [inst_term(env, t) for t in ts])
        case Conn(c, As): return Conn(c, [inst_form(env, A) for A in As])
        case Quant(q, v, A): return Quant(q, v, inst_form(env, A))
        case _: raise MatchError

def inst_goal(env: Env, goal: Goal) -> Goal:
    return Goal([inst_form(env, f) for f in goal.left], 
                [inst_form(env, f) for f in goal.right])

def solve_goal(g: Goal) -> Optional[Tuple[Form, Env]]:
    for p in g.left:
        for q in g.right:
            try:
                env = unify(p, q, dict())
                return (p, env)
            except UnifyError: pass
    return None


# PROOFS

class Proof:
    vindex: Dict[str, int]
    goals: List[Goal]
    trace: List[Form]

    def __init__(self, goal: Goal) -> None:
        self.vindex = dict()
        self.goals = [goal]
        self.trace = []

    def __str__(self) -> str:
        s = ''
        if len(self.goals) == 0: s += 'qed'
        elif len(self.goals) == 1: s += '1 goal:'
        else: s += f'{len(self.goals)} goals:'
        for g in self.goals: s += f'\n  {g}'
        s += '\n\n'
        return s

    def __replace_goal(self, gi: int, *new_goals: Goal) -> None:
        self.goals.pop(gi)
        goals = list(new_goals)
        while len(goals) > 0:
            g = goals.pop()
            sln = solve_goal(g)
            if sln:
                env = sln[1]
                self.goals = [inst_goal(env, h) for h in self.goals]
                goals = [inst_goal(env, h) for h in goals]
                self.trace.append(inst_form(env, sln[0]))
            else:
                self.goals.insert(gi, g)

    def __fresh(self, base: str) -> str:
        if not base in self.vindex:
            self.vindex[base] = 0
        v = base + str(self.vindex[base])
        self.vindex[base] += 1
        return v

    def notL(self, fi: int, gi: int=0) -> bool:
        g = self.goals[gi].copy()
        match g.left.pop(fi):
            case Conn(C.NOT, [A]):
                self.__replace_goal(gi, g.extend([], [A]))
                return True
            case _: return False

    def notR(self, fi: int, gi: int=0) -> bool:
        g = self.goals[gi].copy()
        match g.right.pop(fi):
            case Conn(C.NOT, [A]):
                self.__replace_goal(gi, g.extend([A], []))
                return True
            case _: return False

    def andL(self, fi: int, gi: int=0) -> bool:
        g = self.goals[gi].copy()
        match g.left.pop(fi):
            case Conn(C.AND, [A, B]):
                self.__replace_goal(gi, g.extend([A, B], []))
                return True
            case _: return False

    def andR(self, fi: int, gi: int=0) -> bool:
        g = self.goals[gi].copy()
        match g.right.pop(fi):
            case Conn(C.AND, [A, B]):
                self.__replace_goal(gi, g.extend([], [A]), g.extend([], [B]))
                return True
            case _: return False

    def orL(self, fi: int, gi: int=0) -> bool:
        g = self.goals[gi].copy()
        match g.left.pop(fi):
            case Conn(C.OR, [A, B]):
                self.__replace_goal(gi, g.extend([A], []), g.extend([B], []))
                return True
            case _: return False

    def orR(self, fi: int, gi: int=0) -> bool:
        g = self.goals[gi].copy()
        match g.right.pop(fi):
            case Conn(C.OR, [A, B]):
                self.__replace_goal(gi, g.extend([], [A, B]))
                return True
            case _: return False

    def impliesL(self, fi: int, gi: int=0) -> bool:
        g = self.goals[gi].copy()
        match g.left.pop(fi):
            case Conn(C.IMPLIES, [A, B]):
                self.__replace_goal(gi, g.extend([], [A]), g.extend([B], []))
                return True
            case _: return False

    def impliesR(self, fi: int, gi: int=0) -> bool:
        g = self.goals[gi].copy()
        match g.right.pop(fi):
            case Conn(C.IMPLIES, [A, B]):
                self.__replace_goal(gi, g.extend([A], [B]))
                return True
            case _: return False

    def iffL(self, fi: int, gi: int=0) -> bool:
        g = self.goals[gi].copy()
        match g.left.pop(fi):
            case Conn(C.IFF, [A, B]):
                self.__replace_goal(gi, g.extend([A, B], []), g.extend([], [A, B]))
                return True
            case _: return False

    def iffR(self, fi: int, gi: int=0) -> bool:
        g = self.goals[gi].copy()
        match g.right.pop(fi):
            case Conn(C.IFF, [A, B]):
                self.__replace_goal(gi, g.extend([A], [B]), g.extend([B], [A]))
                return True
            case _: return False

    def allL(self, fi: int, gi: int=0) -> bool:
        g = self.goals[gi].copy()
        match g.left[fi]:
            case Quant(Q.ALL, x, A):
                A = A.subst_bound(Var(self.__fresh(x)))
                g.left.insert(fi, A)
                self.__replace_goal(gi, g)
                return True
            case _: return False

    def allR(self, fi: int, gi: int=0) -> bool:
        g = self.goals[gi].copy()
        match g.right.pop(fi):
            case Quant(Q.ALL, x, A):
                vs = self.goals[gi].vars()
                A = A.subst_bound(Param(self.__fresh(x), vs))
                self.__replace_goal(gi, g.extend([], [A]))
                return True
            case _: return False
    
    def existsL(self, fi: int, gi: int=0) -> bool:
        g = self.goals[gi].copy()
        match g.left.pop(fi):
            case Quant(Q.EX, x, A):
                vs = self.goals[gi].vars()
                A = A.subst_bound(Param(self.__fresh(x), vs))
                self.__replace_goal(gi, g.extend([A], []))
                return True
            case _: return False

    def existsR(self, fi: int, gi: int=0) -> bool:
        g = self.goals[gi].copy()
        match g.right[fi]:
            case Quant(Q.EX, x, A):
                A = A.subst_bound(Var(self.__fresh(x)))
                g.right.insert(fi, A)
                self.__replace_goal(gi, g)
                return True
            case _: return False

    def rule(self, name: str) -> bool:
        if name[-1] == 'L': n = len(self.goals[0].left)
        else: n = len(self.goals[0].right)
        m = getattr(self, name)
        return any(m(i, 0) for i in range(n))


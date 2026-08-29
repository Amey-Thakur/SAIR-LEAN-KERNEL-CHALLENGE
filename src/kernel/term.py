# ==============================================================================
# File: term.py
# Description: The three things a Lean environment is built out of: hierarchical
#   names, universe levels, and expressions in de Bruijn form. Everything the
#   checker does above this file is a fold over these types, so they are kept
#   immutable and hashable, which is what makes caching sound later on.
# Usage: from src.kernel.term import Expr, Level, Name
# Tech Stack: Python 3.10+, standard library only
# ==============================================================================

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional


# -- names -----------------------------------------------------------------

@dataclass(frozen=True)
class Name:
    """A hierarchical name. `Nat.add` is str(str(anonymous, "Nat"), "add")."""
    parts: tuple = ()

    @staticmethod
    def anonymous() -> "Name":
        return Name(())

    def child_str(self, s: str) -> "Name":
        return Name(self.parts + (s,))

    def child_num(self, i: int) -> "Name":
        return Name(self.parts + (i,))

    def __str__(self) -> str:
        return ".".join(str(p) for p in self.parts) or "[anonymous]"


ANON = Name.anonymous()


# -- universe levels -------------------------------------------------------

@dataclass(frozen=True)
class Level:
    """Universe levels. `kind` is zero, succ, max, imax or param."""
    kind: str
    a: Optional["Level"] = None
    b: Optional["Level"] = None
    name: Optional[Name] = None

    def __str__(self) -> str:
        if self.kind == "zero":
            return "0"
        if self.kind == "succ":
            return f"({self.a}+1)"
        if self.kind == "max":
            return f"max({self.a},{self.b})"
        if self.kind == "imax":
            return f"imax({self.a},{self.b})"
        return str(self.name)


ZERO = Level("zero")


def succ(l: Level) -> Level:
    return Level("succ", a=l)


def mk_max(a: Level, b: Level) -> Level:
    return Level("max", a=a, b=b)


def mk_imax(a: Level, b: Level) -> Level:
    return Level("imax", a=a, b=b)


def param(n: Name) -> Level:
    return Level("param", name=n)


def level_offset(l: Level) -> tuple:
    """Split a level into its base and the number of succs on top, which is
    the form the ordering test below wants."""
    n = 0
    while l.kind == "succ":
        n += 1
        l = l.a
    return l, n


def instantiate_level(l: Level, subst: dict) -> Level:
    """Replace universe parameters by levels."""
    if l.kind == "param":
        return subst.get(l.name, l)
    if l.kind == "succ":
        return succ(instantiate_level(l.a, subst))
    if l.kind in ("max", "imax"):
        a = instantiate_level(l.a, subst)
        b = instantiate_level(l.b, subst)
        return normalise_level(Level(l.kind, a=a, b=b))
    return l


def normalise_level(l: Level) -> Level:
    """Enough normalisation to decide the equalities a kernel actually meets:
    imax collapses when its right side is known zero or known successor, and
    max folds when both sides share a base."""
    if l.kind == "succ":
        return succ(normalise_level(l.a))
    if l.kind in ("max", "imax"):
        a, b = normalise_level(l.a), normalise_level(l.b)
        if l.kind == "imax":
            if b.kind == "zero":
                return ZERO
            if b.kind == "succ":
                return normalise_level(mk_max(a, b))
            if level_eq(a, b):
                return a
            return mk_imax(a, b)
        if a.kind == "zero":
            return b
        if b.kind == "zero":
            return a
        ba, na = level_offset(a)
        bb, nb = level_offset(b)
        if level_eq(ba, bb):
            return a if na >= nb else b
        return mk_max(a, b)
    return l


def level_eq(x: Level, y: Level) -> bool:
    """Structural equality after normalisation."""
    x, y = normalise_level(x), normalise_level(y)
    if x.kind != y.kind:
        return False
    if x.kind == "zero":
        return True
    if x.kind == "param":
        return x.name == y.name
    if x.kind == "succ":
        return level_eq(x.a, y.a)
    return level_eq(x.a, y.a) and level_eq(x.b, y.b)


def level_leq(x: Level, y: Level) -> bool:
    """Is x <= y for every assignment of its parameters. Conservative: a false
    answer only ever costs a rejection the caller can report honestly."""
    x, y = normalise_level(x), normalise_level(y)
    if level_eq(x, y):
        return True
    if x.kind == "zero":
        return True
    bx, nx = level_offset(x)
    by, ny = level_offset(y)
    if level_eq(bx, by):
        return nx <= ny
    if x.kind == "max":
        return level_leq(x.a, y) and level_leq(x.b, y)
    if y.kind == "max":
        return level_leq(x, y.a) or level_leq(x, y.b)
    if y.kind == "imax":
        return level_leq(x, y.b)
    if x.kind == "imax":
        return level_leq(x.a, y) and level_leq(x.b, y)
    return False


# -- expressions -----------------------------------------------------------

@dataclass(frozen=True)
class Expr:
    """A term. `kind` is one of bvar, sort, const, app, lam, forall, let, lit,
    proj or mdata. Bound variables are de Bruijn indices, so a term carries no
    names that matter and alpha equivalence is plain equality."""
    kind: str
    idx: int = 0
    level: Optional[Level] = None
    name: Optional[Name] = None
    levels: tuple = ()
    fn: Optional["Expr"] = None
    arg: Optional["Expr"] = None
    dom: Optional["Expr"] = None
    body: Optional["Expr"] = None
    val: Optional["Expr"] = None
    lit: object = None
    binder: str = "default"
    _hash: int = field(default=0, compare=False, repr=False)

    def __str__(self) -> str:
        k = self.kind
        if k == "bvar":
            return f"#{self.idx}"
        if k == "sort":
            return f"Sort {self.level}"
        if k == "const":
            return str(self.name)
        if k == "app":
            return f"({self.fn} {self.arg})"
        if k == "lam":
            return f"(fun : {self.dom} => {self.body})"
        if k == "forall":
            return f"({self.dom} -> {self.body})"
        if k == "let":
            return f"(let {self.val} in {self.body})"
        if k == "lit":
            return repr(self.lit)
        if k == "proj":
            return f"({self.val}.{self.idx})"
        return str(self.body)


def bvar(i: int) -> Expr:
    return Expr("bvar", idx=i)


def sort(l: Level) -> Expr:
    return Expr("sort", level=l)


def const(n: Name, levels: tuple = ()) -> Expr:
    return Expr("const", name=n, levels=tuple(levels))


def app(f: Expr, a: Expr) -> Expr:
    return Expr("app", fn=f, arg=a)


def apps(f: Expr, args) -> Expr:
    for a in args:
        f = app(f, a)
    return f


def lam(dom: Expr, body: Expr, name: Name = ANON, binder: str = "default") -> Expr:
    return Expr("lam", dom=dom, body=body, name=name, binder=binder)


def pi(dom: Expr, body: Expr, name: Name = ANON, binder: str = "default") -> Expr:
    return Expr("forall", dom=dom, body=body, name=name, binder=binder)


def let_(dom: Expr, val: Expr, body: Expr, name: Name = ANON) -> Expr:
    return Expr("let", dom=dom, val=val, body=body, name=name)


def lit_nat(n: int) -> Expr:
    return Expr("lit", lit=n)


def lit_str(s: str) -> Expr:
    return Expr("lit", lit=s)


def proj(type_name: Name, idx: int, struct: Expr) -> Expr:
    return Expr("proj", name=type_name, idx=idx, val=struct)


def unfold_apps(e: Expr):
    """Split f a b c into (f, [a, b, c])."""
    args = []
    while e.kind == "app":
        args.append(e.arg)
        e = e.fn
    args.reverse()
    return e, args


def lift(e: Expr, d: int, cutoff: int = 0) -> Expr:
    """Shift free de Bruijn indices by d."""
    if d == 0:
        return e
    k = e.kind
    if k == "bvar":
        return bvar(e.idx + d) if e.idx >= cutoff else e
    if k == "app":
        return app(lift(e.fn, d, cutoff), lift(e.arg, d, cutoff))
    if k in ("lam", "forall"):
        return Expr(k, dom=lift(e.dom, d, cutoff), body=lift(e.body, d, cutoff + 1),
                    name=e.name, binder=e.binder)
    if k == "let":
        return let_(lift(e.dom, d, cutoff), lift(e.val, d, cutoff),
                    lift(e.body, d, cutoff + 1), e.name)
    if k == "proj":
        return proj(e.name, e.idx, lift(e.val, d, cutoff))
    if k == "mdata":
        return Expr("mdata", body=lift(e.body, d, cutoff))
    return e


def instantiate(e: Expr, v: Expr, depth: int = 0) -> Expr:
    """Replace bound variable `depth` by v, the substitution beta needs."""
    k = e.kind
    if k == "bvar":
        if e.idx == depth:
            return lift(v, depth)
        return bvar(e.idx - 1) if e.idx > depth else e
    if k == "app":
        return app(instantiate(e.fn, v, depth), instantiate(e.arg, v, depth))
    if k in ("lam", "forall"):
        return Expr(k, dom=instantiate(e.dom, v, depth),
                    body=instantiate(e.body, v, depth + 1),
                    name=e.name, binder=e.binder)
    if k == "let":
        return let_(instantiate(e.dom, v, depth), instantiate(e.val, v, depth),
                    instantiate(e.body, v, depth + 1), e.name)
    if k == "proj":
        return proj(e.name, e.idx, instantiate(e.val, v, depth))
    if k == "mdata":
        return Expr("mdata", body=instantiate(e.body, v, depth))
    return e


def instantiate_levels(e: Expr, subst: dict) -> Expr:
    """Replace universe parameters throughout a term."""
    if not subst:
        return e
    k = e.kind
    if k == "sort":
        return sort(instantiate_level(e.level, subst))
    if k == "const":
        return const(e.name, tuple(instantiate_level(l, subst) for l in e.levels))
    if k == "app":
        return app(instantiate_levels(e.fn, subst), instantiate_levels(e.arg, subst))
    if k in ("lam", "forall"):
        return Expr(k, dom=instantiate_levels(e.dom, subst),
                    body=instantiate_levels(e.body, subst),
                    name=e.name, binder=e.binder)
    if k == "let":
        return let_(instantiate_levels(e.dom, subst), instantiate_levels(e.val, subst),
                    instantiate_levels(e.body, subst), e.name)
    if k == "proj":
        return proj(e.name, e.idx, instantiate_levels(e.val, subst))
    if k == "mdata":
        return Expr("mdata", body=instantiate_levels(e.body, subst))
    return e

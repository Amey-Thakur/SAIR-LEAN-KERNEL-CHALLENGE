# ==============================================================================
# File: inductives.py
# Description: The standard inductive types, built by hand for the tests. These
#   are the shapes the derivation has to get right: a recursive constructor, a
#   parameter, an index, a proposition that may eliminate large and one that may
#   not. Everything is written out rather than read from an export, so a test
#   failure points at the deriver and not at the reader.
# Usage: from tests.inductives import nat_block, list_block
# Tech Stack: Python 3.10+
# ==============================================================================

from src.kernel.environment import Declaration
from src.kernel.inductive import InductiveBlock
from src.kernel.term import (ANON, Name, ZERO, app, apps, bvar, const, mk_max,
                             param, pi, sort, succ)

TYPE0 = sort(succ(ZERO))
PROP = sort(ZERO)
U = ANON.child_str("u")
V = ANON.child_str("w")


def n(*parts) -> Name:
    out = ANON
    for p in parts:
        out = out.child_str(p)
    return out


def ind(name, ty, ctors, levels=(), nparams=0, nindices=0):
    return Declaration("inductive", name, levels, ty, num_params=nparams,
                       num_indices=nindices, ctors=tuple(ctors))


def ctor(name, ty, induct, cidx, nfields, levels=(), nparams=0):
    return Declaration("ctor", name, levels, ty, induct=induct, cidx=cidx,
                       num_fields=nfields, num_params=nparams)


def block(types, ctors, levels=(), nparams=0):
    return InductiveBlock(level_params=tuple(levels), num_params=nparams,
                          types=tuple(types), ctors=tuple(ctors), recursors=())


# -- False and True: no fields, the two Prop extremes ------------------------

def false_block():
    return block([ind(n("False"), PROP, [])], [])


def true_block():
    return block(
        [ind(n("True"), PROP, [n("True", "intro")])],
        [ctor(n("True", "intro"), const(n("True")), n("True"), 0, 0)])


# -- Nat: the recursive constructor, and so the induction hypothesis ---------

def nat_block():
    NAT = const(n("Nat"))
    return block(
        [ind(n("Nat"), TYPE0, [n("Nat", "zero"), n("Nat", "succ")])],
        [ctor(n("Nat", "zero"), NAT, n("Nat"), 0, 0),
         ctor(n("Nat", "succ"), pi(NAT, NAT), n("Nat"), 1, 1)])


# -- List: a parameter, and recursion under it ------------------------------

def list_block():
    """List.{u} (a : Type u) : Type u, with nil and cons."""
    LU = const(n("List"), (param(U),))
    return block(
        [ind(n("List"), pi(sort(succ(param(U))), sort(succ(param(U)))),
             [n("List", "nil"), n("List", "cons")], levels=(U,),
             nparams=1)],
        # nil : forall a, List a
        [ctor(n("List", "nil"), pi(sort(succ(param(U))), app(LU, bvar(0))),
              n("List"), 0, 0, levels=(U,), nparams=1),
         # cons : forall a, a -> List a -> List a
         ctor(n("List", "cons"),
              pi(sort(succ(param(U))),
                 pi(bvar(0),
                    pi(app(LU, bvar(1)), app(LU, bvar(2))))),
              n("List"), 1, 2, levels=(U,), nparams=1)],
        levels=(U,), nparams=1)


# -- Eq: an index, one constructor with no fields, so K-like ----------------

def eq_block():
    """Eq.{u} {a : Sort u} (x : a) : a -> Prop, with refl."""
    EQ = const(n("Eq"), (param(U),))
    return block(
        [ind(n("Eq"),
             pi(sort(param(U)), pi(bvar(0), pi(bvar(1), PROP))),
             [n("Eq", "refl")], levels=(U,), nparams=2, nindices=1)],
        # refl : forall a (x : a), Eq a x x
        [ctor(n("Eq", "refl"),
              pi(sort(param(U)), pi(bvar(0), apps(EQ, [bvar(1), bvar(0), bvar(0)]))),
              n("Eq"), 0, 0, levels=(U,), nparams=2)],
        levels=(U,), nparams=2)


# -- And and Or: the subsingleton rule, both ways ---------------------------

def and_block():
    """And (a b : Prop) : Prop. Both fields are proofs, so it eliminates
    large."""
    AND = const(n("And"))
    return block(
        [ind(n("And"), pi(PROP, pi(PROP, PROP)), [n("And", "intro")], nparams=2)],
        [ctor(n("And", "intro"),
              pi(PROP, pi(PROP, pi(bvar(1), pi(bvar(1),
                 apps(AND, [bvar(3), bvar(2)]))))),
              n("And"), 0, 2, nparams=2)],
        nparams=2)


def or_block():
    """Or (a b : Prop) : Prop. Two constructors, so Prop elimination only."""
    OR = const(n("Or"))
    return block(
        [ind(n("Or"), pi(PROP, pi(PROP, PROP)),
             [n("Or", "inl"), n("Or", "inr")], nparams=2)],
        [ctor(n("Or", "inl"),
              pi(PROP, pi(PROP, pi(bvar(1), apps(OR, [bvar(2), bvar(1)])))),
              n("Or"), 0, 1, nparams=2),
         ctor(n("Or", "inr"),
              pi(PROP, pi(PROP, pi(bvar(0), apps(OR, [bvar(2), bvar(1)])))),
              n("Or"), 1, 1, nparams=2)],
        nparams=2)


# -- Prod: two parameters in two universes, landing in their max ------------

def prod_block():
    """Prod.{u,w} (a : Type u) (b : Type w) : Type (max u w)."""
    UU, WW = param(U), param(V)
    TU, TW = sort(succ(UU)), sort(succ(WW))
    TM = sort(succ(mk_max(UU, WW)))
    PR = const(n("Prod"), (UU, WW))
    return block(
        [ind(n("Prod"), pi(TU, pi(TW, TM)), [n("Prod", "mk")],
             levels=(U, V), nparams=2)],
        [ctor(n("Prod", "mk"),
              pi(TU, pi(TW, pi(bvar(1), pi(bvar(1),
                 apps(PR, [bvar(3), bvar(2)]))))),
              n("Prod"), 0, 2, levels=(U, V), nparams=2)],
        levels=(U, V), nparams=2)


ALL = {"False": false_block, "True": true_block, "Nat": nat_block,
       "List": list_block, "Eq": eq_block, "And": and_block,
       "Or": or_block, "Prod": prod_block}

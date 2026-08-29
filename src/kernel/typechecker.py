# ==============================================================================
# File: typechecker.py
# Description: The part that is allowed to say yes. Weak head normalisation with
#   beta, zeta, delta and iota, definitional equality with eta and proof
#   irrelevance, and type inference for the core term language. Anything it
#   cannot decide raises Declined rather than guessing, because a checker that
#   guesses is a checker that eventually accepts a false proof.
# Usage: from src.kernel.typechecker import TypeChecker
# Tech Stack: Python 3.10+, standard library only
# ==============================================================================

from __future__ import annotations

from .environment import Declaration, Environment
from .term import (Expr, Level, Name, ZERO, apps, bvar, const, instantiate,
                   instantiate_levels, level_eq, lift, mk_imax,
                   normalise_level, pi, sort, succ, unfold_apps)


class Rejected(Exception):
    """The environment is not well typed, and here is why."""


class Declined(Exception):
    """This checker does not handle the input, and will not pretend to."""


class TypeChecker:
    def __init__(self, env: Environment, fuel: int = 200_000):
        self.env = env
        self.fuel = fuel

    # -- fuel ---------------------------------------------------------------

    def _burn(self) -> None:
        self.fuel -= 1
        if self.fuel <= 0:
            raise Declined("reduction budget exhausted")

    # -- reduction ----------------------------------------------------------

    def whnf(self, e: Expr) -> Expr:
        """Weak head normal form: reduce only enough to expose the head."""
        while True:
            self._burn()
            k = e.kind
            if k == "mdata":
                e = e.body
                continue
            if k == "let":
                e = instantiate(e.body, e.val)
                continue
            if k == "app":
                fn, args = unfold_apps(e)
                head = self.whnf_core_head(fn)
                if head.kind == "lam" and args:
                    # beta, consuming as many arguments as there are binders
                    i = 0
                    while head.kind == "lam" and i < len(args):
                        head = instantiate(head.body, args[i])
                        i += 1
                    e = apps(head, args[i:])
                    continue
                reduced = self.try_delta_iota(head, args)
                if reduced is not None:
                    e = reduced
                    continue
                return apps(head, args) if head is not fn else e
            nxt = self.try_delta_iota(e, [])
            if nxt is not None:
                e = nxt
                continue
            return e

    def whnf_core_head(self, e: Expr) -> Expr:
        """Reduce a head position without touching its arguments."""
        while True:
            self._burn()
            if e.kind == "mdata":
                e = e.body
                continue
            if e.kind == "let":
                e = instantiate(e.body, e.val)
                continue
            return e

    def try_delta_iota(self, head: Expr, args: list):
        """Unfold a definition, or fire a recursor. None when neither applies."""
        if head.kind != "const":
            return None
        decl = self.env.get(head.name)
        if decl is None:
            raise Rejected(f"unknown constant {head.name}")

        if decl.kind == "recursor":
            return self.try_iota(decl, head, args)

        if decl.has_value:
            if len(decl.level_params) != len(head.levels):
                raise Rejected(f"universe arity mismatch at {head.name}")
            subst = dict(zip(decl.level_params, head.levels))
            return apps(instantiate_levels(decl.value, subst), args)
        return None

    def try_iota(self, rec: Declaration, head: Expr, args: list):
        """Fire a recursor when its major premise is a constructor application."""
        major_pos = rec.num_params + rec.num_motives + rec.num_minors + rec.num_indices
        if len(args) <= major_pos:
            return None
        major = self.whnf(args[major_pos])
        cfn, cargs = unfold_apps(major)
        if cfn.kind != "const":
            return None
        cdecl = self.env.get(cfn.name)
        if cdecl is None or cdecl.kind != "ctor":
            return None
        rule = next((r for r in rec.rules if r.ctor == cfn.name), None)
        if rule is None:
            raise Rejected(f"no recursor rule for {cfn.name} in {rec.name}")
        # the rule expects the recursor's parameters and motives, then the
        # constructor's own fields, then whatever was applied after the major
        take = cargs[len(cargs) - rule.nfields:] if rule.nfields else []
        subst = dict(zip(rec.level_params, head.levels))
        rhs = instantiate_levels(rule.rhs, subst)
        rhs = apps(rhs, args[:major_pos - rec.num_indices] + take)
        return apps(rhs, args[major_pos + 1:])

    # -- definitional equality ---------------------------------------------

    def is_def_eq(self, a: Expr, b: Expr) -> bool:
        """Three strategies, tried in order of cost. Each one may fail without
        settling the question, so none of them may return False on its own."""
        if a is b:
            return True
        self._burn()
        a, b = self.whnf(a), self.whnf(b)

        if self.structurally_eq(a, b):
            return True

        # eta: fun x => f x is f
        if a.kind == "lam" and b.kind != "lam":
            return self.is_def_eq(a.body, Expr("app", fn=lift(b, 1), arg=bvar(0)))
        if b.kind == "lam" and a.kind != "lam":
            return self.is_def_eq(Expr("app", fn=lift(a, 1), arg=bvar(0)), b.body)

        # proof irrelevance: any two proofs of one proposition are the same
        if self.is_proof(a) and self.is_proof(b):
            return self.is_def_eq(self.infer(a), self.infer(b))
        return False

    def structurally_eq(self, a: Expr, b: Expr) -> bool:
        """Equality on the heads, once both sides are already in whnf."""
        if a.kind != b.kind:
            return False
        if a.kind == "bvar":
            return a.idx == b.idx
        if a.kind == "sort":
            return level_eq(a.level, b.level)
        if a.kind == "lit":
            return type(a.lit) is type(b.lit) and a.lit == b.lit
        if a.kind == "const":
            return (a.name == b.name
                    and len(a.levels) == len(b.levels)
                    and all(level_eq(x, y) for x, y in zip(a.levels, b.levels)))
        if a.kind in ("lam", "forall"):
            return self.is_def_eq(a.dom, b.dom) and self.is_def_eq(a.body, b.body)
        if a.kind == "proj":
            return a.idx == b.idx and self.is_def_eq(a.val, b.val)
        if a.kind == "app":
            fa, aa = unfold_apps(a)
            fb, ab = unfold_apps(b)
            return (len(aa) == len(ab) and self.is_def_eq(fa, fb)
                    and all(self.is_def_eq(x, y) for x, y in zip(aa, ab)))
        return False

    def is_proof(self, e: Expr) -> bool:
        try:
            ty = self.whnf(self.infer(e))
            s = self.whnf(self.infer(ty))
        except (Rejected, Declined):
            return False
        return s.kind == "sort" and level_eq(s.level, ZERO)

    # -- inference ----------------------------------------------------------

    def infer(self, e: Expr, ctx: tuple = ()) -> Expr:
        """The type of e in a context of binder types, innermost first."""
        self._burn()
        k = e.kind

        if k == "bvar":
            if e.idx >= len(ctx):
                raise Rejected(f"loose bound variable #{e.idx}")
            return lift(ctx[e.idx], e.idx + 1)

        if k == "sort":
            return sort(succ(e.level))

        if k == "const":
            decl = self.env.get(e.name)
            if decl is None:
                raise Rejected(f"unknown constant {e.name}")
            if len(decl.level_params) != len(e.levels):
                raise Rejected(f"universe arity mismatch at {e.name}")
            return instantiate_levels(decl.type, dict(zip(decl.level_params, e.levels)))

        if k == "app":
            fty = self.whnf(self.infer(e.fn, ctx))
            if fty.kind != "forall":
                raise Rejected(f"applying a non function: {e.fn}")
            aty = self.infer(e.arg, ctx)
            if not self.is_def_eq(aty, fty.dom):
                raise Rejected(f"argument type mismatch at {e}")
            return instantiate(fty.body, e.arg)

        if k == "lam":
            self.ensure_sort(e.dom, ctx)
            bty = self.infer(e.body, (e.dom,) + ctx)
            return pi(e.dom, bty, e.name, e.binder)

        if k == "forall":
            la = self.ensure_sort(e.dom, ctx)
            lb = self.ensure_sort(e.body, (e.dom,) + ctx)
            return sort(normalise_level(mk_imax(la, lb)))

        if k == "let":
            self.ensure_sort(e.dom, ctx)
            vty = self.infer(e.val, ctx)
            if not self.is_def_eq(vty, e.dom):
                raise Rejected("let value does not match its ascription")
            return self.infer(instantiate(e.body, e.val), ctx)

        if k == "lit":
            if isinstance(e.lit, int):
                return const(_name("Nat"))
            return const(_name("String"))

        if k == "mdata":
            return self.infer(e.body, ctx)

        if k == "proj":
            raise Declined("structure projections are not implemented")

        raise Declined(f"unhandled term kind {k}")

    def ensure_sort(self, e: Expr, ctx: tuple = ()) -> Level:
        s = self.whnf(self.infer(e, ctx))
        if s.kind != "sort":
            raise Rejected(f"expected a type, found {s}")
        return s.level

    # -- declarations -------------------------------------------------------

    def check_declaration(self, decl: Declaration) -> None:
        """A declaration is well formed when its type is a type, and its value,
        if it has one, inhabits that type."""
        if decl.is_unsafe:
            raise Declined(f"unsafe declaration {decl.name}")
        self.ensure_sort(decl.type)
        if decl.has_value:
            vty = self.infer(decl.value)
            if not self.is_def_eq(vty, decl.type):
                raise Rejected(f"{decl.name} does not have its declared type")


def _name(s: str) -> Name:
    return Name.anonymous().child_str(s)

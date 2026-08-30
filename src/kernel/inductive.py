# ==============================================================================
# File: inductive.py
# Description: The part that refuses to believe the export. An inductive block
#   arrives carrying its own constructors and recursors, and every structural
#   claim in it is an assertion the exporter makes rather than a fact: how many
#   parameters, how many fields a constructor has, which recursors exist and how
#   they reduce. This module derives all of that from the inductive types alone
#   and checks the export against what it derived, because a checker that
#   registers exported recursors as given ends up holding an inhabitant of the
#   empty type.
# Usage: from src.kernel.inductive import InductiveBlock, check_block
# Tech Stack: Python 3.10+, standard library only
# ==============================================================================

from __future__ import annotations

from dataclasses import dataclass

from .errors import Declined, Rejected
from .term import (Expr, Level, Name, ZERO, apps, bvar, const, fold_lam,
                   fold_pi, has_const, level_eq, level_is_zero, level_leq,
                   level_never_zero, lift, param, sort, unfold_apps, unfold_pi)

MOTIVE = Name.anonymous().child_str("motive")
MINOR = Name.anonymous().child_str("minor")
MAJOR = Name.anonymous().child_str("t")
IH = Name.anonymous().child_str("ih")


@dataclass
class InductiveBlock:
    """One `inductive` item from the export, kept whole.

    The grouping is the point. A recursor is only meaningful relative to the
    types it was declared with, so flattening the block into loose declarations
    throws away the only thing that says which recursors may exist."""
    level_params: tuple
    num_params: int
    types: tuple
    ctors: tuple
    recursors: tuple

    @property
    def names(self) -> frozenset:
        return frozenset(t.name for t in self.types)

    def declarations(self):
        return list(self.types) + list(self.ctors) + list(self.recursors)


def bvar_occurs(e: Expr, idx: int, off: int = 0) -> bool:
    """Does the bound variable `idx`, counted at the top level, occur in e."""
    if e is None:
        return False
    k = e.kind
    if k == "bvar":
        return e.idx == idx + off
    if k in ("lam", "forall"):
        return bvar_occurs(e.dom, idx, off) or bvar_occurs(e.body, idx, off + 1)
    if k == "let":
        return (bvar_occurs(e.dom, idx, off) or bvar_occurs(e.val, idx, off)
                or bvar_occurs(e.body, idx, off + 1))
    if k == "app":
        return bvar_occurs(e.fn, idx, off) or bvar_occurs(e.arg, idx, off)
    if k in ("proj", "mdata"):
        return bvar_occurs(e.val or e.body, idx, off)
    return False


class Deriver:
    """Derives what an inductive block is entitled to, and compares.

    Positions are tracked absolutely, counted outwards from the first parameter,
    and turned into de Bruijn indices only at the point of use. Every telescope
    the recursor quantifies over is laid out in the same order:

        params (P) . motives (n) . minors (M) . indices . major

    so a binder at absolute position `p`, seen from a depth of `d` binders, is
    `bvar(d - 1 - p)`. Domains lifted out of the original declarations are
    relocated with an explicit cutoff, never by eye."""

    def __init__(self, tc, block: InductiveBlock):
        self.tc = tc
        self.block = block
        self.P = block.num_params
        self.n = len(block.types)
        self.M = len(block.ctors)
        self.names = block.names
        self.us = tuple(param(nm) for nm in block.level_params)
        self.index_of = {t.name: j for j, t in enumerate(block.types)}

        self.params = []        # binders of the shared parameter telescope
        self.indices = []       # per type
        self.sorts = []         # per type, the Level it lands in
        self.fields = []        # per ctor
        self.result_args = []   # per ctor, the args of its result type
        self.ctor_ind = []      # per ctor, which type it builds

    # -- telescoping --------------------------------------------------------

    def pi_binders(self, e: Expr, limit=None, what=""):
        """Split a Pi telescope, reducing when the head is not yet a binder."""
        binders, body = unfold_pi(e, limit)
        while limit is not None and len(binders) < limit:
            body = self.tc.whnf(body)
            more, body = unfold_pi(body, limit - len(binders))
            if not more:
                raise Rejected(f"{what}: expected {limit} parameters, "
                               f"found {len(binders)}")
            binders += more
        return binders, body

    def ctx_of(self, binders, upto):
        """The context TypeChecker.infer wants: binder types, innermost first."""
        return tuple(d for _, d, _ in reversed(binders[:upto]))

    # -- validation ---------------------------------------------------------

    def read_types(self):
        b = self.block
        for j, t in enumerate(b.types):
            if tuple(t.level_params) != tuple(b.level_params):
                raise Rejected(f"{t.name}: universe parameters differ from its block")
            params, rest = self.pi_binders(t.type, self.P, str(t.name))
            indices, body = self.pi_binders(rest)
            body = self.tc.whnf(body)
            if body.kind != "sort":
                raise Rejected(f"{t.name}: an inductive type must end in a sort")
            if j == 0:
                self.params = params
            elif len(params) != len(self.params):
                raise Rejected(f"{t.name}: parameter telescope differs from its block")
            else:
                for i, ((_, a, _), (_, c, _)) in enumerate(zip(params, self.params)):
                    if not self.tc.is_def_eq(a, c):
                        raise Rejected(f"{t.name}: parameter {i} differs from its block")
            self.indices.append(indices)
            self.sorts.append(body.level)
            if t.num_params != self.P:
                raise Rejected(f"{t.name}: declared numParams does not match its block")
            if t.num_indices != len(indices):
                raise Rejected(f"{t.name}: declared numIndices is {t.num_indices}, "
                               f"the type has {len(indices)}")

    def read_ctors(self):
        b = self.block
        seen = {j: [] for j in range(self.n)}
        for c, decl in enumerate(b.ctors):
            if decl.induct not in self.index_of:
                raise Rejected(f"{decl.name}: constructs {decl.induct}, "
                               f"which is not in this block")
            j = self.index_of[decl.induct]
            self.ctor_ind.append(j)
            if tuple(decl.level_params) != tuple(b.level_params):
                raise Rejected(f"{decl.name}: universe parameters differ from its block")

            params, rest = self.pi_binders(decl.type, self.P, str(decl.name))
            for i, ((_, a, _), (_, e, _)) in enumerate(zip(params, self.params)):
                if not self.tc.is_def_eq(a, e):
                    raise Rejected(f"{decl.name}: parameter {i} is not the "
                                   f"parameter its inductive declares")
            fields, body = self.pi_binders(rest)
            m = len(fields)
            body = self.tc.whnf(body)
            head, args = unfold_apps(body)

            if head.kind != "const" or head.name != decl.induct:
                raise Rejected(f"{decl.name}: does not build {decl.induct}")
            if len(head.levels) != len(self.us) or not all(
                    level_eq(x, y) for x, y in zip(head.levels, self.us)):
                raise Rejected(f"{decl.name}: builds its inductive at the wrong "
                               f"universes")
            if len(args) != self.P + len(self.indices[j]):
                raise Rejected(f"{decl.name}: applies {decl.induct} to "
                               f"{len(args)} arguments")
            for i in range(self.P):
                if not self.tc.is_def_eq(args[i], bvar(m + self.P - 1 - i)):
                    raise Rejected(f"{decl.name}: parameter {i} is not passed "
                                   f"through to its own result type")

            allb = list(self.params) + list(fields)
            for i, (_, dom, _) in enumerate(fields):
                self.check_positivity(dom, f"{decl.name}, field {i}")
                s = self.tc.ensure_sort(dom, self.ctx_of(allb, self.P + i))
                u = self.sorts[j]
                if not level_is_zero(u) and not level_leq(s, u):
                    raise Rejected(f"{decl.name}: field {i} lives in a universe "
                                   f"its inductive does not reach")

            if decl.num_fields != m:
                raise Rejected(f"{decl.name}: declared numFields is "
                               f"{decl.num_fields}, the type has {m}")
            if decl.num_params != self.P:
                raise Rejected(f"{decl.name}: declared numParams does not match")
            if decl.cidx != len(seen[j]):
                raise Rejected(f"{decl.name}: declared cidx is {decl.cidx}, "
                               f"it is constructor {len(seen[j])}")
            seen[j].append(decl.name)
            self.fields.append(fields)
            self.result_args.append(args)

        for j, t in enumerate(self.block.types):
            if tuple(t.ctors) != tuple(seen[j]):
                raise Rejected(f"{t.name}: its constructor list does not match "
                               f"the constructors exported for it")

    def check_positivity(self, t: Expr, where: str) -> None:
        """The inductive may appear in a field only as the result of that
        field, never to the left of an arrow and never inside its own
        arguments. Without this, a single negative occurrence is enough to
        write a fixed point and prove False."""
        if not has_const(t, self.names):
            return
        binders, body = unfold_pi(t)
        for _, dom, _ in binders:
            if has_const(dom, self.names):
                raise Rejected(f"{where}: the inductive being defined occurs to "
                               f"the left of an arrow")
        head, args = unfold_apps(body)
        if head.kind == "const" and head.name in self.names:
            for a in args:
                if has_const(a, self.names):
                    raise Rejected(f"{where}: the inductive being defined occurs "
                                   f"in its own arguments")
            return
        # The occurrence is under some other type former, as in `List Tree`.
        # That is a nested inductive, which is not unsound, only unimplemented
        # here, and the difference matters: rejecting it would call a great deal
        # of ordinary mathematics false.
        raise Declined(f"{where}: nested inductives are not implemented")

    # -- elimination --------------------------------------------------------

    def allows_large_elim(self) -> bool:
        """May the motive land anywhere, or only in Prop.

        A type whose universe is a bare parameter might be instantiated at Prop,
        so it is treated as one. That single conservatism is what stops
        `inductive MyBool.{u} : Sort u | tt | ff` from being handed a
        large-eliminating recursor, which proof irrelevance would then turn into
        a proof of False."""
        if all(level_never_zero(s) for s in self.sorts):
            return True
        if self.n != 1:
            return False
        ctors = [c for c in range(self.M) if self.ctor_ind[c] == 0]
        if not ctors:
            return True                     # nothing to be irrelevant about
        if len(ctors) > 1:
            return False
        c = ctors[0]
        fields = self.fields[c]
        m = len(fields)
        allb = list(self.params) + list(fields)
        idx_args = self.result_args[c][self.P:]
        for i, (_, dom, _) in enumerate(fields):
            s = self.tc.ensure_sort(dom, self.ctx_of(allb, self.P + i))
            if level_is_zero(s):
                continue                    # a proof, and so irrelevant anyway
            if not any(bvar_occurs(a, m - 1 - i) for a in idx_args):
                return False
        return True

    def is_k_like(self, j: int) -> bool:
        """K reduction rests on proof irrelevance, so it needs a genuine Prop
        with exactly one constructor that carries nothing."""
        if not level_is_zero(self.sorts[j]):
            return False
        ctors = [c for c in range(self.M) if self.ctor_ind[c] == j]
        return len(ctors) == 1 and not self.fields[ctors[0]]

    def motive_level(self, rec_decl) -> Level:
        """The universe the motive lands in, taken from the exported recursor's
        own level parameters and then checked against what is permitted."""
        big = self.allows_large_elim()
        base = tuple(self.block.level_params)
        got = tuple(rec_decl.level_params)
        if big:
            if len(got) != len(base) + 1 or got[1:] != base:
                raise Rejected(f"{rec_decl.name}: expected one motive universe "
                               f"followed by the universes of its block")
            return param(got[0])
        if got != base:
            raise Rejected(f"{rec_decl.name}: this inductive may only eliminate "
                           f"into Prop, so its recursor takes no motive universe")
        return ZERO

    # -- the derived pieces -------------------------------------------------

    def ind_app(self, j, depth, idx_base):
        args = [bvar(depth - 1 - i) for i in range(self.P)]
        args += [bvar(depth - 1 - (idx_base + k))
                 for k in range(len(self.indices[j]))]
        return apps(const(self.block.types[j].name, self.us), args)

    def motive_type(self, jj, mlevel):
        """motive_jj : forall indices, I_jj params indices -> Sort mlevel."""
        D0 = self.P + jj
        binders = [(nm, lift(dom, jj, k), bi)
                   for k, (nm, dom, bi) in enumerate(self.indices[jj])]
        D = D0 + len(binders)
        binders.append((MAJOR, self.ind_app(jj, D, D0), "default"))
        return fold_pi(binders, sort(mlevel))

    def minor_type(self, c, mlevel):
        """The premise for one constructor: its fields, an hypothesis for each
        recursive field, and the motive at the value that constructor builds."""
        P, n = self.P, self.n
        j = self.ctor_ind[c]
        D0 = P + n + c
        fields = self.fields[c]
        m = len(fields)
        binders = [(nm, lift(dom, n + c, i), bi)
                   for i, (nm, dom, bi) in enumerate(fields)]

        r = 0
        for i, (_, dom, _) in enumerate(fields):
            if not has_const(dom, self.names):
                continue
            here = lift(lift(dom, n + c, i), m + r - i, 0)
            ys, head = unfold_pi(here)
            f, args = unfold_apps(head)
            jp = self.index_of[f.name]
            Dy = D0 + m + r + len(ys)
            f_ref = bvar(Dy - 1 - (D0 + i))
            ys_refs = [bvar(len(ys) - 1 - k) for k in range(len(ys))]
            body = apps(bvar(Dy - 1 - (P + jp)),
                        args[P:] + [apps(f_ref, ys_refs)])
            binders.append((IH, fold_pi(ys, body), "default"))
            r += 1

        D2 = D0 + m + r
        idx = [lift(lift(a, r, 0), n + c, m + r)
               for a in self.result_args[c][P:]]
        built = apps(const(self.block.ctors[c].name, self.us),
                     [bvar(D2 - 1 - i) for i in range(P)]
                     + [bvar(m + r - 1 - i) for i in range(m)])
        return fold_pi(binders, apps(bvar(D2 - 1 - (P + j)), idx + [built]))

    def outer_binders(self, mlevel):
        """params . motives . minors, shared by the recursor and every rule."""
        binders = list(self.params)
        binders += [(MOTIVE, self.motive_type(jj, mlevel), "implicit")
                    for jj in range(self.n)]
        binders += [(MINOR, self.minor_type(cc, mlevel), "default")
                    for cc in range(self.M)]
        return binders

    def recursor_type(self, j, mlevel):
        P, n, M = self.P, self.n, self.M
        binders = self.outer_binders(mlevel)
        binders += [(nm, lift(dom, n + M, k), bi)
                    for k, (nm, dom, bi) in enumerate(self.indices[j])]
        nidx = len(self.indices[j])
        D = P + n + M + nidx
        binders.append((MAJOR, self.ind_app(j, D, P + n + M), "default"))
        D2 = D + 1
        idx_refs = [bvar(D2 - 1 - (P + n + M + k)) for k in range(nidx)]
        body = apps(bvar(D2 - 1 - (P + j)), idx_refs + [bvar(0)])
        return fold_pi(binders, body)

    def recursor_rhs(self, c, mlevel):
        """What the recursor becomes on one constructor: the matching minor
        premise, applied to the fields and to a recursive call per recursive
        field. Abstracted over params, motives, minors and fields, and over
        nothing else, which is the shape iota reduction then supplies."""
        P, n, M = self.P, self.n, self.M
        fields = self.fields[c]
        m = len(fields)
        binders = self.outer_binders(mlevel)
        binders += [(nm, lift(dom, n + M, i), bi)
                    for i, (nm, dom, bi) in enumerate(fields)]
        D3 = P + n + M + m

        ih_vals = []
        for i, (_, dom, _) in enumerate(fields):
            if not has_const(dom, self.names):
                continue
            here = lift(lift(dom, n + M, i), m - i, 0)
            ys, head = unfold_pi(here)
            f, args = unfold_apps(head)
            jp = self.index_of[f.name]
            Dy = D3 + len(ys)
            outer = [bvar(Dy - 1 - i2) for i2 in range(P)]
            outer += [bvar(Dy - 1 - (P + jj)) for jj in range(n)]
            outer += [bvar(Dy - 1 - (P + n + cc)) for cc in range(M)]
            f_ref = bvar(Dy - 1 - (P + n + M + i))
            ys_refs = [bvar(len(ys) - 1 - k) for k in range(len(ys))]
            call = apps(const(self.rec_name(jp), self.rec_levels(mlevel)),
                        outer + args[P:] + [apps(f_ref, ys_refs)])
            ih_vals.append(fold_lam(ys, call))

        body = apps(bvar(D3 - 1 - (P + n + c)),
                    [bvar(m - 1 - i) for i in range(m)] + ih_vals)
        return fold_lam(binders, body)

    def rec_name(self, j) -> Name:
        return self.block.types[j].name.child_str("rec")

    def rec_levels(self, mlevel) -> tuple:
        return ((mlevel,) + self.us
                if self.allows_large_elim() else self.us)

    # -- the comparison -----------------------------------------------------

    def check_recursors(self):
        derived = {self.rec_name(j): j for j in range(self.n)}
        for decl in self.block.recursors:
            j = derived.get(decl.name)
            if j is None:
                raise Rejected(
                    f"{decl.name}: this inductive block produces "
                    f"{sorted(str(k) for k in derived)} and nothing else, so "
                    f"there is no such recursor to register")
            mlevel = self.motive_level(decl)

            want = {"numParams": self.P, "numIndices": len(self.indices[j]),
                    "numMotives": self.n, "numMinors": self.M,
                    "k": self.is_k_like(j)}
            got = {"numParams": decl.num_params, "numIndices": decl.num_indices,
                   "numMotives": decl.num_motives, "numMinors": decl.num_minors,
                   "k": bool(decl.k)}
            for field, expected in want.items():
                if got[field] != expected:
                    raise Rejected(f"{decl.name}: declared {field} is "
                                   f"{got[field]}, derived {expected}")

            if not self.tc.is_def_eq(decl.type, self.recursor_type(j, mlevel)):
                raise Rejected(f"{decl.name}: its type is not the eliminator "
                               f"this inductive gives rise to")

            mine = [c for c in range(self.M) if self.ctor_ind[c] == j]
            by_ctor = {self.block.ctors[c].name: c for c in mine}
            if len(decl.rules) != len(mine):
                raise Rejected(f"{decl.name}: has {len(decl.rules)} rules, "
                               f"its inductive has {len(mine)} constructors")
            for rule in decl.rules:
                c = by_ctor.get(rule.ctor)
                if c is None:
                    raise Rejected(f"{decl.name}: has a rule for {rule.ctor}, "
                                   f"which it does not construct")
                if rule.nfields != len(self.fields[c]):
                    raise Rejected(f"{decl.name}: the rule for {rule.ctor} "
                                   f"claims {rule.nfields} fields, the "
                                   f"constructor has {len(self.fields[c])}")
                if not self.tc.is_def_eq(rule.rhs, self.recursor_rhs(c, mlevel)):
                    raise Rejected(f"{decl.name}: the rule for {rule.ctor} does "
                                   f"not reduce the way this inductive says")

    def derived_recursors(self):
        """The recursors this block is entitled to, as declarations.

        The checker does not use this to fill in a missing recursor, because an
        export that omits one is simply an export in which nothing can call it.
        It exists so that the derivation can be exercised directly, and so that
        what is derived can be read rather than only compared against."""
        from .environment import Declaration, RecursorRule

        self.read_types()
        self.read_ctors()
        big = self.allows_large_elim()
        mname = Name.anonymous().child_str("v")
        while mname in self.block.level_params:
            mname = mname.child_str("v")
        mlevel = param(mname) if big else ZERO
        levels = ((mname,) + tuple(self.block.level_params) if big
                  else tuple(self.block.level_params))

        out = []
        for j in range(self.n):
            mine = [c for c in range(self.M) if self.ctor_ind[c] == j]
            out.append(Declaration(
                "recursor", self.rec_name(j), levels,
                self.recursor_type(j, mlevel),
                num_params=self.P, num_indices=len(self.indices[j]),
                num_motives=self.n, num_minors=self.M,
                rules=tuple(RecursorRule(self.block.ctors[c].name,
                                         len(self.fields[c]),
                                         self.recursor_rhs(c, mlevel))
                            for c in mine),
                k=self.is_k_like(j)))
        return out

    def run(self):
        self.read_types()
        self.read_ctors()
        self.check_recursors()


def check_block(tc, block: InductiveBlock) -> None:
    """Validate one inductive block, or refuse it."""
    Deriver(tc, block).run()

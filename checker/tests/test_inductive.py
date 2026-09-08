# ==============================================================================
# File: test_inductive.py
# Description: Tests for the part that refuses to believe the export. The
#   acceptance half checks that the derived eliminators are the ones Lean
#   generates and that they actually reduce. The refusal half is the point of
#   the file: every structural claim an export makes about an inductive block
#   is tampered with in turn, and each one has to be caught, because two of
#   them are proofs of False in the arena's own suite.
# Usage: python -m pytest tests -q
# Tech Stack: Python 3.10+, pytest
# ==============================================================================

from dataclasses import replace

import pytest

from src.harness.check_export import ACCEPTED, REJECTED, check_stream
from src.kernel.environment import Declaration, Environment, RecursorRule
from src.kernel.errors import Declined, Rejected
from src.kernel.inductive import Deriver, check_block
from src.kernel.term import (ANON, ZERO, apps, bvar, const, param, pi, sort,
                             succ)
from src.kernel.typechecker import TypeChecker

from .inductives import ALL, PROP, TYPE0, block, ctor, ind, n


def derive(b):
    """Derive the recursors of a block, and hand back the block carrying them
    together with a checker over an environment that holds it."""
    env = Environment()
    env.add_block(b)
    tc = TypeChecker(env, fuel=5_000_000)
    recs = Deriver(tc, b).derived_recursors()
    full = replace(b, recursors=tuple(recs))
    env2 = Environment()
    env2.add_block(full)
    return full, TypeChecker(env2, fuel=5_000_000)


# -- what the derivation produces ------------------------------------------

@pytest.mark.parametrize("name", sorted(ALL))
def test_every_standard_inductive_derives_a_well_formed_eliminator(name):
    b = ALL[name]()
    full, tc = derive(b)
    assert full.recursors, f"{name} produced no recursor"
    for r in full.recursors:
        # If the de Bruijn arithmetic were wrong this would not be a type.
        tc.ensure_sort(r.type)


@pytest.mark.parametrize("name", sorted(ALL))
def test_the_derived_block_checks_against_itself(name):
    full, tc = derive(ALL[name]())
    check_block(tc, full)


def test_nat_gets_the_eliminator_it_should():
    full, tc = derive(ALL["Nat"]())
    rec, = full.recursors
    assert str(rec.name) == "Nat.rec"
    assert (rec.num_params, rec.num_motives, rec.num_minors, rec.num_indices) \
        == (0, 1, 2, 0)
    assert not rec.k
    assert [str(r.ctor) for r in rec.rules] == ["Nat.zero", "Nat.succ"]
    # The successor case takes the field and an hypothesis about it.
    assert [r.nfields for r in rec.rules] == [0, 1]


def test_a_proposition_with_two_constructors_may_not_eliminate_large():
    full, _ = derive(ALL["Or"]())
    rec, = full.recursors
    assert rec.level_params == ()          # no motive universe to choose
    # The motive lands in Prop, written into the type rather than chosen.
    assert "Sort 0" in str(rec.type)


def test_a_proposition_whose_fields_are_proofs_may():
    full, _ = derive(ALL["And"]())
    rec, = full.recursors
    assert len(rec.level_params) == 1


def test_only_a_subsingleton_prop_is_k_like():
    assert derive(ALL["True"]())[0].recursors[0].k
    assert derive(ALL["Eq"]())[0].recursors[0].k
    assert not derive(ALL["Nat"]())[0].recursors[0].k
    assert not derive(ALL["Or"]())[0].recursors[0].k


# -- and that it reduces ----------------------------------------------------

def test_the_derived_recursor_actually_fires():
    """Nat.rec M z s (Nat.succ Nat.zero) is s Nat.zero (Nat.rec M z s Nat.zero).

    This is the check that the rule's right hand side is right rather than
    merely well formed: it runs iota reduction through the derived rule."""
    full, _ = derive(ALL["Nat"]())
    env = Environment()
    env.add_block(full)
    NAT, ZE = const(n("Nat")), const(n("Nat", "zero"))
    SU = const(n("Nat", "succ"))
    env.add(Declaration("axiom", n("M"), (), pi(NAT, TYPE0)))
    env.add(Declaration("axiom", n("z"), (), apps(const(n("M")), [ZE])))
    env.add(Declaration("axiom", n("s"), (),
                        pi(NAT, pi(apps(const(n("M")), [bvar(0)]),
                                   apps(const(n("M")), [apps(SU, [bvar(1)])])))))
    tc = TypeChecker(env, fuel=5_000_000)

    lvl = succ(ZERO)
    M, z, s = const(n("M")), const(n("z")), const(n("s"))
    REC = const(n("Nat", "rec"), (lvl,))
    one = apps(SU, [ZE])

    got = tc.whnf(apps(REC, [M, z, s, one]))
    want = apps(s, [ZE, apps(REC, [M, z, s, ZE])])
    assert tc.is_def_eq(got, want), f"got {got}"

    # And the base case reduces to the base premise.
    assert tc.is_def_eq(tc.whnf(apps(REC, [M, z, s, ZE])), z)


def test_the_derived_recursor_is_well_typed_at_its_own_rule():
    """The successor rule, applied to the arguments its type quantifies over,
    must land in the type the eliminator promises."""
    full, tc = derive(ALL["Nat"]())
    rec, = full.recursors
    tc.ensure_sort(rec.type)
    for rule in rec.rules:
        # An ill scoped right hand side would have a loose bound variable.
        tc.infer(rule.rhs)


# -- the arena's own attacks ------------------------------------------------

def test_a_fabricated_recursor_is_rejected(extra_rec_export):
    code, msg = check_stream(extra_rec_export)
    assert code == REJECTED
    assert "rogue" in msg


def test_a_prop_that_might_be_is_not_given_large_elimination(large_elim_export):
    code, msg = check_stream(large_elim_export)
    assert code == REJECTED
    assert "MyBool" in msg


def test_the_genuine_part_of_that_export_is_still_accepted(large_elim_export):
    """Everything before the tampering is real Lean output, recursors and rules
    included. If the derivation were merely strict rather than correct, this
    would be rejected too."""
    code, msg = check_stream(large_elim_export[:85])
    assert code == ACCEPTED, msg
    assert "5 declarations" in msg


# -- tampering with the structural claims -----------------------------------

def check_tampered(full):
    env = Environment()
    env.add_block(full)
    tc = TypeChecker(env, fuel=5_000_000)
    check_block(tc, full)


def test_a_constructor_that_lies_about_its_field_count_is_rejected():
    full, _ = derive(ALL["Nat"]())
    bad = replace(full, ctors=(full.ctors[0],
                               replace(full.ctors[1], num_fields=0)))
    with pytest.raises(Rejected, match="numFields"):
        check_tampered(bad)


def test_a_constructor_that_lies_about_its_index_is_rejected():
    full, _ = derive(ALL["Or"]())
    bad = replace(full, ctors=(replace(full.ctors[0], cidx=1), full.ctors[1]))
    with pytest.raises(Rejected, match="cidx"):
        check_tampered(bad)


def test_a_type_that_lies_about_its_parameter_count_is_rejected():
    full, _ = derive(ALL["List"]())
    bad = replace(full, types=(replace(full.types[0], num_params=0),))
    with pytest.raises(Rejected, match="numParams"):
        check_tampered(bad)


def test_a_type_that_lies_about_its_index_count_is_rejected():
    full, _ = derive(ALL["Eq"]())
    bad = replace(full, types=(replace(full.types[0], num_indices=0),))
    with pytest.raises(Rejected, match="numIndices"):
        check_tampered(bad)


def test_an_extra_recursor_is_rejected():
    full, _ = derive(ALL["Nat"]())
    rogue = replace(full.recursors[0], name=n("Nat", "rogue"))
    bad = replace(full, recursors=full.recursors + (rogue,))
    with pytest.raises(Rejected, match="no such recursor"):
        check_tampered(bad)


def test_a_recursor_whose_type_was_swapped_is_rejected():
    full, _ = derive(ALL["Nat"]())
    bad = replace(full, recursors=(
        replace(full.recursors[0], type=pi(const(n("Nat")), const(n("Nat")))),))
    with pytest.raises(Rejected):
        check_tampered(bad)


def test_a_recursor_rule_that_reduces_the_wrong_way_is_rejected():
    full, _ = derive(ALL["Nat"]())
    rec = full.recursors[0]
    zero_rule, succ_rule = rec.rules
    swapped = (RecursorRule(zero_rule.ctor, zero_rule.nfields, succ_rule.rhs),
               succ_rule)
    bad = replace(full, recursors=(replace(rec, rules=swapped),))
    with pytest.raises(Rejected, match="does not reduce"):
        check_tampered(bad)


def test_a_rule_claiming_the_wrong_field_count_is_rejected():
    full, _ = derive(ALL["Nat"]())
    rec = full.recursors[0]
    z, s = rec.rules
    bad = replace(full, recursors=(
        replace(rec, rules=(z, RecursorRule(s.ctor, 0, s.rhs))),))
    with pytest.raises(Rejected, match="fields"):
        check_tampered(bad)


def test_a_recursor_that_claims_extra_minor_premises_is_rejected():
    full, _ = derive(ALL["Nat"]())
    bad = replace(full, recursors=(replace(full.recursors[0], num_minors=3),))
    with pytest.raises(Rejected, match="numMinors"):
        check_tampered(bad)


def test_a_recursor_that_claims_k_it_has_not_earned_is_rejected():
    full, _ = derive(ALL["Nat"]())
    bad = replace(full, recursors=(replace(full.recursors[0], k=True),))
    with pytest.raises(Rejected, match="k"):
        check_tampered(bad)


def test_a_constructor_of_a_foreign_inductive_is_rejected():
    full, _ = derive(ALL["Nat"]())
    bad = replace(full, ctors=(replace(full.ctors[0], induct=n("Other")),
                               full.ctors[1]))
    with pytest.raises(Rejected, match="not in this block"):
        check_tampered(bad)


# -- the checks that have nothing to do with the export's honesty -----------

def test_a_negative_occurrence_is_rejected():
    """inductive Bad : Type | mk : (Bad -> False) -> Bad.

    Strict positivity is not a style rule. A single occurrence to the left of
    an arrow is enough to write a fixed point and derive False."""
    BAD = const(n("Bad"))
    b = block(
        [ind(n("Bad"), TYPE0, [n("Bad", "mk")])],
        [ctor(n("Bad", "mk"), pi(pi(BAD, PROP), BAD), n("Bad"), 0, 1)])
    env = Environment()
    env.add_block(b)
    with pytest.raises(Rejected, match="left of an arrow"):
        check_block(TypeChecker(env, fuel=5_000_000), b)


def test_a_nested_inductive_is_declined_rather_than_rejected():
    """inductive Tree | node : List Tree -> Tree.

    The occurrence is under another type former. That is not a soundness
    failure, it is a feature this checker does not implement, and calling it a
    rejection would call a great deal of ordinary mathematics false."""
    TREE = const(n("Tree"))
    env = Environment()
    env.add(Declaration("axiom", n("List"), (), pi(TYPE0, TYPE0)))
    b = block(
        [ind(n("Tree"), TYPE0, [n("Tree", "node")])],
        [ctor(n("Tree", "node"),
              pi(apps(const(n("List")), [TREE]), TREE), n("Tree"), 0, 1)])
    env.add_block(b)
    with pytest.raises(Declined, match="nested"):
        check_block(TypeChecker(env, fuel=5_000_000), b)


def test_a_field_escaping_its_universe_is_rejected():
    """inductive Big : Type 0 | mk : Type 0 -> Big would let a universe hold
    something the size of itself."""
    b = block(
        [ind(n("Big"), TYPE0, [n("Big", "mk")])],
        [ctor(n("Big", "mk"), pi(TYPE0, const(n("Big"))), n("Big"), 0, 1)])
    env = Environment()
    env.add_block(b)
    with pytest.raises(Rejected, match="universe"):
        check_block(TypeChecker(env, fuel=5_000_000), b)


def test_a_constructor_that_builds_the_wrong_type_is_rejected():
    b = block(
        [ind(n("A"), TYPE0, [n("A", "mk")]),
         ind(n("B"), TYPE0, [])],
        [ctor(n("A", "mk"), const(n("B")), n("A"), 0, 0)])
    env = Environment()
    env.add_block(b)
    with pytest.raises(Rejected, match="does not build"):
        check_block(TypeChecker(env, fuel=5_000_000), b)


def test_an_inductive_that_does_not_end_in_a_sort_is_rejected():
    b = block([ind(n("Weird"), const(n("Nat")), [])], [])
    env = Environment()
    env.add(Declaration("axiom", n("Nat"), (), TYPE0))
    env.add_block(b)
    with pytest.raises(Rejected, match="sort"):
        check_block(TypeChecker(env, fuel=5_000_000), b)


def test_a_universe_polymorphic_two_constructor_type_stays_small():
    """The shape behind the arena's large-elim attack, built directly:
    `Sort u` might be `Prop`, so two constructors means Prop elimination."""
    U = ANON.child_str("u")
    MB = const(n("MyBool"), (param(U),))
    b = block(
        [ind(n("MyBool"), sort(param(U)),
             [n("MyBool", "tt"), n("MyBool", "ff")], levels=(U,))],
        [ctor(n("MyBool", "tt"), MB, n("MyBool"), 0, 0, levels=(U,)),
         ctor(n("MyBool", "ff"), MB, n("MyBool"), 1, 0, levels=(U,))],
        levels=(U,))
    full, _ = derive(b)
    rec, = full.recursors
    assert tuple(rec.level_params) == (U,), "no motive universe may be taken"
    assert "Sort 0" in str(rec.type), "the motive must be pinned to Prop"

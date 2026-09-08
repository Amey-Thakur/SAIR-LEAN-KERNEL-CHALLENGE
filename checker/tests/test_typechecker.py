# ==============================================================================
# File: test_typechecker.py
# Description: Tests for the part that is allowed to say yes. Half of these
#   check that it accepts what it should; the other half check that it refuses
#   what it should, which is the half that matters, because a checker that only
#   ever accepts passes the first half perfectly.
# Usage: python -m pytest tests -q
# Tech Stack: Python 3.10+, pytest
# ==============================================================================

import pytest

from src.export_format.reader import read_export
from src.kernel.environment import Declaration, Environment
from src.kernel.term import (ANON, Name, ZERO, app, bvar, const, lam, pi, proj,
                             sort, succ)
from src.kernel.typechecker import Declined, Rejected, TypeChecker


def n(*parts) -> Name:
    out = ANON
    for p in parts:
        out = out.child_str(p)
    return out


TYPE = sort(succ(ZERO))
PROP = sort(ZERO)


def base_env() -> Environment:
    """A type, an inhabitant, and a proposition with a proof of it."""
    env = Environment()
    env.add(Declaration("axiom", n("A"), (), TYPE))
    env.add(Declaration("axiom", n("a"), (), const(n("A"))))
    env.add(Declaration("axiom", n("P"), (), PROP))
    env.add(Declaration("axiom", n("h1"), (), const(n("P"))))
    env.add(Declaration("axiom", n("h2"), (), const(n("P"))))
    return env


@pytest.fixture
def tc():
    return TypeChecker(base_env())


# -- what it should accept -------------------------------------------------

def test_a_sort_lives_one_level_up(tc):
    assert tc.infer(PROP) == TYPE


def test_the_identity_gets_a_function_type(tc):
    A = const(n("A"))
    ty = tc.infer(lam(A, bvar(0)))
    assert ty.kind == "forall" and ty.dom == A and ty.body == A


def test_applying_the_identity_returns_the_argument_type(tc):
    A, a = const(n("A")), const(n("a"))
    assert tc.is_def_eq(tc.infer(app(lam(A, bvar(0)), a)), A)


def test_beta_reduction_happens_in_whnf(tc):
    a = const(n("a"))
    assert tc.whnf(app(lam(const(n("A")), bvar(0)), a)) == a


def test_a_definition_unfolds_when_the_head_is_needed():
    env = base_env()
    env.add(Declaration("def", n("a2"), (), const(n("A")), const(n("a"))))
    tc = TypeChecker(env)
    assert tc.whnf(const(n("a2"))) == const(n("a"))
    assert tc.is_def_eq(const(n("a2")), const(n("a")))


def test_a_let_is_substituted_away(tc):
    from src.kernel.term import let_
    A, a = const(n("A")), const(n("a"))
    assert tc.whnf(let_(A, a, bvar(0))) == a


def test_two_proofs_of_one_proposition_are_equal(tc):
    # Proof irrelevance. Without it, a kernel rejects perfectly good terms
    # that differ only in which proof was supplied.
    assert tc.is_def_eq(const(n("h1")), const(n("h2")))


def test_eta_makes_a_wrapper_equal_to_what_it_wraps():
    env = base_env()
    A = const(n("A"))
    env.add(Declaration("axiom", n("f"), (), pi(A, A)))
    tc = TypeChecker(env)
    f = const(n("f"))
    assert tc.is_def_eq(lam(A, app(f, bvar(0))), f)


def test_a_function_type_is_a_type(tc):
    A = const(n("A"))
    assert tc.ensure_sort(pi(A, A)) is not None


def test_a_pi_into_prop_stays_a_prop(tc):
    # imax is what makes Prop impredicative, and it is easy to get wrong in a
    # way nothing else notices.
    s = tc.infer(pi(const(n("A")), const(n("P"))))
    assert s.kind == "sort"
    from src.kernel.term import level_eq
    assert level_eq(s.level, ZERO)


def test_a_well_typed_export_checks_end_to_end(well_typed):
    env = read_export(well_typed)
    tc = TypeChecker(env)
    for decl in env:
        tc.check_declaration(decl)


# -- what it should refuse -------------------------------------------------

def test_two_distinct_axioms_are_not_equal(tc):
    assert not tc.is_def_eq(const(n("A")), const(n("a")))


def test_applying_a_non_function_is_rejected(tc):
    with pytest.raises(Rejected):
        tc.infer(app(const(n("a")), const(n("a"))))


def test_an_argument_of_the_wrong_type_is_rejected(tc):
    A = const(n("A"))
    with pytest.raises(Rejected):
        tc.infer(app(lam(A, bvar(0)), const(n("A"))))


def test_a_loose_bound_variable_is_rejected(tc):
    with pytest.raises(Rejected):
        tc.infer(bvar(0))


def test_an_unknown_constant_is_rejected(tc):
    with pytest.raises(Rejected):
        tc.infer(const(n("nowhere")))


def test_a_universe_arity_mismatch_is_rejected(tc):
    with pytest.raises(Rejected):
        tc.infer(const(n("A"), (ZERO,)))


def test_a_binder_whose_domain_is_not_a_type_is_rejected(tc):
    with pytest.raises(Rejected):
        tc.infer(lam(const(n("a")), bvar(0)))


def test_a_definition_that_misses_its_type_is_rejected():
    env = base_env()
    env.add(Declaration("def", n("bad"), (), const(n("A")), PROP))
    tc = TypeChecker(env)
    with pytest.raises(Rejected):
        tc.check_declaration(env.get(n("bad")))


def test_an_ill_typed_export_is_rejected(ill_typed):
    env = read_export(ill_typed)
    tc = TypeChecker(env)
    with pytest.raises(Rejected):
        for decl in env:
            tc.check_declaration(decl)


# -- what it should decline ------------------------------------------------

def test_a_projection_is_declined_not_guessed(tc):
    with pytest.raises(Declined):
        tc.infer(proj(n("A"), 0, const(n("a"))))


def test_an_unsafe_declaration_is_declined():
    env = base_env()
    env.add(Declaration("def", n("u"), (), const(n("A")), const(n("a")),
                        is_unsafe=True))
    tc = TypeChecker(env)
    with pytest.raises(Declined):
        tc.check_declaration(env.get(n("u")))


def test_running_out_of_fuel_declines_rather_than_hangs():
    env = base_env()
    tc = TypeChecker(env, fuel=3)
    with pytest.raises(Declined):
        for _ in range(100):
            tc.whnf(const(n("a")))

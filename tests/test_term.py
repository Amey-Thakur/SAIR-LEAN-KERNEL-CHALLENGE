# ==============================================================================
# File: test_term.py
# Description: Tests for the term language. De Bruijn shifting and substitution
#   are where a kernel goes silently wrong: an off-by-one in `lift` does not
#   crash, it changes which variable a proof is about. These cases pin the
#   arithmetic down, and the level tests pin down the imax rules that decide
#   whether a Pi lands in Prop.
# Usage: python -m pytest tests -q
# Tech Stack: Python 3.10+, pytest
# ==============================================================================

from src.kernel.term import (ANON, Name, ZERO, app, bvar, const, instantiate,
                             instantiate_level, instantiate_levels, lam,
                             level_eq, level_leq, lift, mk_imax, mk_max, param,
                             pi, sort, succ, unfold_apps)

u = Name.anonymous().child_str("u")
v = Name.anonymous().child_str("v")


# -- names -----------------------------------------------------------------

def test_name_is_hierarchical_and_hashable():
    n = ANON.child_str("Nat").child_str("add")
    assert str(n) == "Nat.add"
    assert n == ANON.child_str("Nat").child_str("add")
    assert len({n, ANON.child_str("Nat").child_str("add")}) == 1


def test_numeric_components_stay_distinct_from_strings():
    assert ANON.child_num(1) != ANON.child_str("1")


# -- levels ----------------------------------------------------------------

def test_imax_with_zero_on_the_right_is_zero():
    # This is the rule that makes Prop impredicative: A -> Prop is a Prop
    # however large A is.
    assert level_eq(mk_imax(succ(succ(ZERO)), ZERO), ZERO)


def test_imax_with_a_successor_on_the_right_becomes_max():
    assert level_eq(mk_imax(succ(ZERO), succ(ZERO)), succ(ZERO))


def test_max_folds_when_both_sides_share_a_base():
    assert level_eq(mk_max(param(u), succ(param(u))), succ(param(u)))


def test_max_of_distinct_parameters_does_not_collapse():
    assert not level_eq(mk_max(param(u), param(v)), param(u))


def test_leq_is_reflexive_and_zero_is_least():
    assert level_leq(ZERO, param(u))
    assert level_leq(param(u), param(u))
    assert not level_leq(succ(param(u)), param(u))


def test_instantiating_a_level_parameter():
    assert level_eq(instantiate_level(succ(param(u)), {u: succ(ZERO)}),
                    succ(succ(ZERO)))


# -- shifting and substitution ---------------------------------------------

def test_lift_moves_free_variables_and_leaves_bound_ones():
    # fun _ => #1 has one free variable, #0 under the binder is bound.
    e = lam(sort(ZERO), app(bvar(0), bvar(1)))
    shifted = lift(e, 1)
    assert shifted.body.fn == bvar(0)
    assert shifted.body.arg == bvar(2)


def test_lift_by_zero_is_the_identity():
    e = lam(sort(ZERO), bvar(3))
    assert lift(e, 0) is e


def test_instantiate_substitutes_and_renumbers():
    # (fun _ => #0 #1) applied to c becomes c #0, not c #1.
    c = const(ANON.child_str("c"))
    body = app(bvar(0), bvar(1))
    assert instantiate(body, c) == app(c, bvar(0))


def test_instantiate_shifts_the_value_under_binders():
    c = bvar(0)
    body = lam(sort(ZERO), bvar(1))
    assert instantiate(body, c).body == bvar(1)


def test_unfold_apps_returns_arguments_left_to_right():
    a, b, c = bvar(0), bvar(1), bvar(2)
    head, args = unfold_apps(app(app(const(ANON.child_str("f")), a), b))
    assert head == const(ANON.child_str("f"))
    assert args == [a, b]
    assert unfold_apps(c) == (c, [])


def test_instantiate_levels_reaches_into_constants_and_sorts():
    e = pi(sort(param(u)), const(ANON.child_str("F"), (param(u),)))
    out = instantiate_levels(e, {u: ZERO})
    assert level_eq(out.dom.level, ZERO)
    assert level_eq(out.body.levels[0], ZERO)

# ==============================================================================
# File: test_dependency_order.py
# Description: Tests that a declaration may only use what the export has already
#   declared. Lean's kernel gets this for free by adding one declaration at a
#   time; a checker that reads the whole file first has to impose it, and the
#   cost of not imposing it is that `def loop : False := loop` checks against
#   its own declared type and the checker returns 0.
# Usage: python -m pytest tests -q
# Tech Stack: Python 3.10+, pytest
# ==============================================================================

import json

import pytest

from src.harness.check_export import ACCEPTED, REJECTED, check_stream
from src.kernel.environment import Declaration, Environment
from src.kernel.errors import Rejected
from src.kernel.term import ZERO, const, sort
from src.kernel.typechecker import TypeChecker

from .inductives import n

L = json.dumps

FALSE_BLOCK = [
    L({"meta": {"format": {"version": "3.1.0"}}}),
    L({"in": 1, "str": {"pre": 0, "str": "False"}}),
    L({"ie": 0, "sort": 0}),
    L({"inductive": {"types": [{"name": 1, "levelParams": [], "type": 0,
                                "numParams": 0, "numIndices": 0, "ctors": [],
                                "isReflexive": False, "isUnsafe": False}],
                     "ctors": [], "recs": []}}),
    L({"in": 2, "str": {"pre": 0, "str": "loop"}}),
    L({"ie": 1, "const": {"name": 1, "us": []}}),
    L({"ie": 2, "const": {"name": 2, "us": []}}),
]


def test_a_definition_may_not_prove_itself():
    """The whole attack in one line: `loop`'s value is `loop`, whose type is
    the `False` it claims to inhabit."""
    code, msg = check_stream(
        FALSE_BLOCK + [L({"def": {"name": 2, "levelParams": [], "type": 1,
                                  "value": 2}})])
    assert code == REJECTED
    assert "loop" in msg


def test_a_theorem_may_not_prove_itself():
    code, _ = check_stream(
        FALSE_BLOCK + [L({"thm": {"name": 2, "levelParams": [], "type": 1,
                                  "value": 2}})])
    assert code == REJECTED


def test_two_definitions_may_not_prove_each_other():
    code, _ = check_stream(FALSE_BLOCK + [
        L({"in": 3, "str": {"pre": 0, "str": "b"}}),
        L({"ie": 3, "const": {"name": 3, "us": []}}),
        L({"def": {"name": 2, "levelParams": [], "type": 1, "value": 3}}),
        L({"def": {"name": 3, "levelParams": [], "type": 1, "value": 2}}),
    ])
    assert code == REJECTED


def test_a_forward_reference_is_rejected():
    """`a : False := b` where b is declared afterwards. Even if b is honest,
    admitting a here would admit the circular case too."""
    code, _ = check_stream(FALSE_BLOCK + [
        L({"in": 3, "str": {"pre": 0, "str": "b"}}),
        L({"ie": 3, "const": {"name": 3, "us": []}}),
        L({"def": {"name": 2, "levelParams": [], "type": 1, "value": 3}}),
        L({"axiom": {"name": 3, "levelParams": [], "type": 1}}),
    ])
    assert code == REJECTED


def test_declarations_in_order_are_accepted(well_typed):
    """The ordinary case is untouched: a real export is already in dependency
    order, because that is the order the environment was built in."""
    code, msg = check_stream(well_typed)
    assert code == ACCEPTED, msg


def test_an_inductive_block_may_refer_to_itself():
    """A constructor mentions its own type, and a recursor rule mentions its
    own recursor. A block is admitted whole for exactly that reason."""
    code, msg = check_stream(FALSE_BLOCK[:4])
    assert code == ACCEPTED, msg


def test_the_rule_is_enforced_before_the_type_is_even_inferred():
    env = Environment()
    env.add(Declaration("def", n("x"), (), sort(ZERO), const(n("x"))))
    tc = TypeChecker(env)
    with pytest.raises(Rejected, match="not declared before"):
        tc.check_declaration(env.get(n("x")))

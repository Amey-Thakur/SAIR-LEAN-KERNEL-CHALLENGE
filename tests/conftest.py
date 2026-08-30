# ==============================================================================
# File: conftest.py
# Description: Puts the repository root on the import path so `src` resolves the
#   same way it does for `python -m src.harness.check_export`, and builds the
#   small exports the other test modules read. The exports are written by hand
#   rather than produced by the reader, so a bug in the reader cannot hide
#   inside its own fixture.
# Usage: python -m pytest tests -q
# Tech Stack: Python 3.10+, pytest
# ==============================================================================

import json
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

META = {"meta": {"kind": "export", "version": "3.1.0", "producer": "tests"}}


def line(obj) -> str:
    return json.dumps(obj)


# A whole environment in fifteen lines. Bool is an axiomatic type, b inhabits
# it, and k is the identity on it, which is the smallest thing that exercises
# binders, application and definitional unfolding at once.
WELL_TYPED = [
    line(META),
    line({"in": 1, "str": {"pre": 0, "str": "Bool"}}),
    line({"in": 2, "str": {"pre": 0, "str": "b"}}),
    line({"in": 3, "str": {"pre": 0, "str": "b2"}}),
    line({"in": 4, "str": {"pre": 0, "str": "k"}}),
    line({"in": 5, "str": {"pre": 0, "str": "kb"}}),
    line({"il": 1, "succ": 0}),
    line({"ie": 0, "sort": 1}),
    line({"axiom": {"name": 1, "levelParams": [], "type": 0}}),
    line({"ie": 1, "const": {"name": 1, "us": []}}),
    line({"axiom": {"name": 2, "levelParams": [], "type": 1}}),
    line({"ie": 2, "const": {"name": 2, "us": []}}),
    line({"def": {"name": 3, "levelParams": [], "type": 1, "value": 2}}),
    line({"ie": 3, "forallE": {"name": 0, "type": 1, "body": 1,
                               "binderInfo": "default"}}),
    line({"ie": 4, "bvar": 0}),
    line({"ie": 5, "lam": {"name": 0, "type": 1, "body": 4,
                           "binderInfo": "default"}}),
    line({"def": {"name": 4, "levelParams": [], "type": 3, "value": 5}}),
    line({"ie": 6, "app": {"fn": 5, "arg": 2}}),
    line({"def": {"name": 5, "levelParams": [], "type": 1, "value": 6}}),
]


@pytest.fixture
def well_typed():
    return list(WELL_TYPED)


@pytest.fixture
def ill_typed():
    """`bad : Bool := Sort 0`. Nothing reduces the two together, so the only
    honest answer is a rejection."""
    return WELL_TYPED + [
        line({"in": 6, "str": {"pre": 0, "str": "bad"}}),
        line({"def": {"name": 6, "levelParams": [], "type": 1, "value": 0}}),
    ]


FIXTURES = Path(__file__).resolve().parent / "fixtures"


def _arena(name):
    """One of the arena's own test exports, kept verbatim. These are the real
    attacks, not reconstructions of them."""
    return (FIXTURES / name).read_text(encoding="utf-8").splitlines()


@pytest.fixture
def extra_rec_export():
    return _arena("extra-rec.ndjson")


@pytest.fixture
def large_elim_export():
    return _arena("large-elim-param.ndjson")


@pytest.fixture
def unsupported():
    """A line the reader does not recognise. It has to decline, because
    skipping an item it cannot read means accepting an environment it never
    saw."""
    return WELL_TYPED + [line({"someFutureItem": {"name": 1}})]

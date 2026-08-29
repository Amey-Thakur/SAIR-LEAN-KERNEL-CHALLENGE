# ==============================================================================
# File: test_reader.py
# Description: Tests for the NDJSON reader. The interesting cases are the ones
#   where it is tempting to be lenient: a forward reference, an item from a
#   later format version, a truncated file. A reader that recovers from any of
#   those is a reader that builds an environment nobody exported.
# Usage: python -m pytest tests -q
# Tech Stack: Python 3.10+, pytest
# ==============================================================================

import json

import pytest

from src.export_format.reader import (MalformedExport, UnsupportedExport,
                                      read_export)
from src.kernel.term import ANON, Name


def n(*parts) -> Name:
    out = ANON
    for p in parts:
        out = out.child_str(p)
    return out


def test_reads_every_declaration_in_order(well_typed):
    env = read_export(well_typed)
    assert [str(d.name) for d in env] == ["Bool", "b", "b2", "k", "kb"]


def test_kinds_survive_the_round_trip(well_typed):
    env = read_export(well_typed)
    assert env.get(n("Bool")).kind == "axiom"
    assert env.get(n("k")).kind == "def"
    assert env.get(n("Bool")).value is None
    assert env.get(n("k")).has_value


def test_expressions_are_rebuilt_not_merely_counted(well_typed):
    k = read_export(well_typed).get(n("k"))
    assert k.type.kind == "forall"
    assert k.value.kind == "lam"
    assert k.value.body.kind == "bvar" and k.value.body.idx == 0


def test_blank_lines_are_ignored(well_typed):
    assert len(read_export(well_typed + ["", "   "])) == 5


def test_a_forward_reference_is_malformed():
    with pytest.raises(MalformedExport):
        read_export([json.dumps({"ie": 0, "const": {"name": 9, "us": []}})])


def test_broken_json_is_malformed():
    with pytest.raises(MalformedExport) as exc:
        read_export(['{"in": 1, "str":'])
    assert "line 1" in str(exc.value)


def test_a_bare_array_is_malformed():
    with pytest.raises(MalformedExport):
        read_export(["[1, 2, 3]"])


def test_an_unknown_item_is_unsupported_rather_than_skipped(unsupported):
    with pytest.raises(UnsupportedExport):
        read_export(unsupported)


def test_an_unknown_level_form_is_unsupported():
    with pytest.raises(UnsupportedExport):
        read_export([json.dumps({"il": 1, "someLevel": 0})])


def test_literals_come_back_as_python_values():
    env = read_export([
        json.dumps({"in": 1, "str": {"pre": 0, "str": "n"}}),
        json.dumps({"ie": 0, "natVal": 7}),
        json.dumps({"ie": 1, "strVal": "hello"}),
        json.dumps({"axiom": {"name": 1, "levelParams": [], "type": 0}}),
    ])
    assert env.get(n("n")).type.lit == 7


def test_declaring_the_same_name_twice_is_refused(well_typed):
    with pytest.raises(KeyError):
        read_export(well_typed + [
            json.dumps({"axiom": {"name": 1, "levelParams": [], "type": 0}})])

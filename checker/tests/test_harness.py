# ==============================================================================
# File: test_harness.py
# Description: Tests for the exit codes, which are the only thing the arena
#   reads. The last test here is the one worth keeping: an input the checker
#   cannot handle must leave with 2, never with 0, because 0 is a claim and
#   silence is not evidence.
# Usage: python -m pytest tests -q
# Tech Stack: Python 3.10+, pytest
# ==============================================================================

from src.harness.check_export import (ACCEPTED, DECLINED, ERROR, REJECTED,
                                      check_stream, main)


def test_a_well_typed_export_exits_zero(well_typed):
    code, msg = check_stream(well_typed)
    assert code == ACCEPTED
    assert "5 declarations" in msg


def test_an_ill_typed_export_exits_one(ill_typed):
    code, msg = check_stream(ill_typed)
    assert code == REJECTED
    assert "bad" in msg


def test_an_unreadable_export_exits_one():
    code, _ = check_stream(['{"in": 1, "str":'])
    assert code == REJECTED


def test_an_unsupported_export_exits_two_not_zero(unsupported):
    code, msg = check_stream(unsupported)
    assert code == DECLINED
    assert msg.startswith("declined")


def test_an_exhausted_budget_declines(well_typed):
    code, _ = check_stream(well_typed, fuel=5)
    assert code == DECLINED


def test_an_empty_input_is_not_an_acceptance_of_anything(well_typed):
    # Zero declarations is a legitimate zero, but it must say so rather than
    # imply the file was checked.
    code, msg = check_stream([])
    assert code == ACCEPTED
    assert "0 declarations" in msg


def test_the_entry_point_reads_a_file(tmp_path, well_typed):
    p = tmp_path / "export.ndjson"
    p.write_text("\n".join(well_typed), encoding="utf-8")
    assert main([str(p)]) == ACCEPTED


def test_the_entry_point_reads_the_arena_environment_variable(
        tmp_path, monkeypatch, well_typed):
    p = tmp_path / "export.ndjson"
    p.write_text("\n".join(well_typed), encoding="utf-8")
    monkeypatch.setenv("IN", str(p))
    assert main([]) == ACCEPTED


def test_a_missing_file_is_an_error_not_an_acceptance(tmp_path):
    assert main([str(tmp_path / "nothing.ndjson")]) == ERROR

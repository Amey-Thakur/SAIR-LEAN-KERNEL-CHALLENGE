# ==============================================================================
# File: reader.py
# Description: Reader for the lean4export NDJSON format, version 3.1.0. Every
#   line is either a primitive that lands in one of three tables, or a
#   declaration that refers to them by index. Nothing here decides whether the
#   environment is true; it only rebuilds what the exporter wrote, and refuses
#   input it does not recognise instead of filling in a default.
# Usage: from src.export_format.reader import read_export
# Tech Stack: Python 3.10+, standard library only
# ==============================================================================

from __future__ import annotations

import json
from typing import Iterable

from ..kernel.environment import Declaration, Environment, RecursorRule
from ..kernel.term import (ANON, Expr, Level, Name, ZERO, app, bvar, const,
                           lam, let_, lit_nat, lit_str, mk_imax, mk_max,
                           param, pi, proj, sort, succ)


class MalformedExport(Exception):
    """The file is not a well formed export."""


class UnsupportedExport(Exception):
    """The file is well formed but uses something this reader does not do."""


class Tables:
    """Names, levels and expressions, each addressed by the integer the
    exporter assigned. Index 0 is the anonymous name and the zero level, which
    the format leaves implicit."""

    def __init__(self):
        self.names = {0: ANON}
        self.levels = {0: ZERO}
        self.exprs = {}

    def name(self, i: int) -> Name:
        try:
            return self.names[i]
        except KeyError:
            raise MalformedExport(f"name {i} used before it was defined")

    def level(self, i: int) -> Level:
        try:
            return self.levels[i]
        except KeyError:
            raise MalformedExport(f"level {i} used before it was defined")

    def expr(self, i: int) -> Expr:
        try:
            return self.exprs[i]
        except KeyError:
            raise MalformedExport(f"expression {i} used before it was defined")


def _read_name(obj: dict, t: Tables) -> bool:
    if "str" in obj and isinstance(obj["str"], dict):
        d = obj["str"]
        t.names[obj["in"]] = t.name(d["pre"]).child_str(d["str"])
        return True
    if "num" in obj and isinstance(obj["num"], dict):
        d = obj["num"]
        t.names[obj["in"]] = t.name(d["pre"]).child_num(d["i"])
        return True
    return False


def _read_level(obj: dict, t: Tables) -> bool:
    i = obj.get("il")
    if i is None:
        return False
    if "succ" in obj:
        t.levels[i] = succ(t.level(obj["succ"]))
    elif "max" in obj:
        a, b = obj["max"]
        t.levels[i] = mk_max(t.level(a), t.level(b))
    elif "imax" in obj:
        a, b = obj["imax"]
        t.levels[i] = mk_imax(t.level(a), t.level(b))
    elif "param" in obj:
        t.levels[i] = param(t.name(obj["param"]))
    else:
        raise UnsupportedExport(f"unknown level form: {sorted(obj)}")
    return True


def _read_expr(obj: dict, t: Tables) -> bool:
    i = obj.get("ie")
    if i is None:
        return False
    if "bvar" in obj:
        t.exprs[i] = bvar(obj["bvar"])
    elif "sort" in obj:
        t.exprs[i] = sort(t.level(obj["sort"]))
    elif "const" in obj:
        d = obj["const"]
        t.exprs[i] = const(t.name(d["name"]), tuple(t.level(u) for u in d["us"]))
    elif "app" in obj:
        d = obj["app"]
        t.exprs[i] = app(t.expr(d["fn"]), t.expr(d["arg"]))
    elif "lam" in obj:
        d = obj["lam"]
        t.exprs[i] = lam(t.expr(d["type"]), t.expr(d["body"]),
                         t.name(d["name"]), d.get("binderInfo", "default"))
    elif "forallE" in obj:
        d = obj["forallE"]
        t.exprs[i] = pi(t.expr(d["type"]), t.expr(d["body"]),
                        t.name(d["name"]), d.get("binderInfo", "default"))
    elif "letE" in obj:
        d = obj["letE"]
        t.exprs[i] = let_(t.expr(d["type"]), t.expr(d["value"]),
                          t.expr(d["body"]), t.name(d["name"]))
    elif "proj" in obj:
        d = obj["proj"]
        t.exprs[i] = proj(t.name(d["typeName"]), d["idx"], t.expr(d["struct"]))
    elif "natVal" in obj:
        t.exprs[i] = lit_nat(int(obj["natVal"]))
    elif "strVal" in obj:
        t.exprs[i] = lit_str(obj["strVal"])
    elif "mdata" in obj:
        t.exprs[i] = Expr("mdata", body=t.expr(obj["mdata"]["expr"]))
    else:
        raise UnsupportedExport(f"unknown expression form: {sorted(obj)}")
    return True


def _levels(ids, t: Tables) -> tuple:
    return tuple(t.name(i) for i in ids)


def _read_decl(obj: dict, t: Tables, env: Environment) -> bool:
    if "axiom" in obj:
        d = obj["axiom"]
        env.add(Declaration("axiom", t.name(d["name"]), _levels(d["levelParams"], t),
                            t.expr(d["type"]), is_unsafe=d.get("isUnsafe", False)))
        return True
    if "def" in obj:
        d = obj["def"]
        env.add(Declaration("def", t.name(d["name"]), _levels(d["levelParams"], t),
                            t.expr(d["type"]), t.expr(d["value"]),
                            is_unsafe=d.get("safety") == "unsafe"))
        return True
    if "thm" in obj:
        d = obj["thm"]
        env.add(Declaration("thm", t.name(d["name"]), _levels(d["levelParams"], t),
                            t.expr(d["type"]), t.expr(d["value"])))
        return True
    if "opaque" in obj:
        d = obj["opaque"]
        env.add(Declaration("opaque", t.name(d["name"]), _levels(d["levelParams"], t),
                            t.expr(d["type"]), is_unsafe=d.get("isUnsafe", False)))
        return True
    if "quot" in obj:
        d = obj["quot"]
        env.add(Declaration("quot", t.name(d["name"]), _levels(d["levelParams"], t),
                            t.expr(d["type"])))
        return True
    if "inductive" in obj:
        d = obj["inductive"]
        for ind in d.get("types", []):
            env.add(Declaration("inductive", t.name(ind["name"]),
                                _levels(ind["levelParams"], t), t.expr(ind["type"]),
                                num_params=ind.get("numParams", 0),
                                num_indices=ind.get("numIndices", 0),
                                ctors=tuple(t.name(c) for c in ind.get("ctors", [])),
                                is_reflexive=ind.get("isReflexive", False),
                                is_unsafe=ind.get("isUnsafe", False)))
        for c in d.get("ctors", []):
            env.add(Declaration("ctor", t.name(c["name"]), _levels(c["levelParams"], t),
                                t.expr(c["type"]), induct=t.name(c["induct"]),
                                cidx=c.get("cidx", 0), num_params=c.get("numParams", 0),
                                num_fields=c.get("numFields", 0),
                                is_unsafe=c.get("isUnsafe", False)))
        for r in d.get("recs", []):
            rules = tuple(RecursorRule(t.name(rr["ctor"]), rr["nfields"],
                                       t.expr(rr["rhs"]))
                          for rr in r.get("rules", []))
            env.add(Declaration("recursor", t.name(r["name"]),
                                _levels(r["levelParams"], t), t.expr(r["type"]),
                                num_params=r.get("numParams", 0),
                                num_indices=r.get("numIndices", 0),
                                num_motives=r.get("numMotives", 0),
                                num_minors=r.get("numMinors", 0),
                                rules=rules, k=r.get("k", False),
                                is_unsafe=r.get("isUnsafe", False)))
        return True
    return False


def read_export(lines: Iterable[str]) -> Environment:
    """Rebuild an environment from the NDJSON export."""
    t = Tables()
    env = Environment()
    meta = None
    for lineno, raw in enumerate(lines, 1):
        raw = raw.strip()
        if not raw:
            continue
        try:
            obj = json.loads(raw)
        except json.JSONDecodeError as exc:
            raise MalformedExport(f"line {lineno} is not JSON: {exc}") from exc
        if not isinstance(obj, dict):
            raise MalformedExport(f"line {lineno} is not an object")
        if "meta" in obj and meta is None and len(obj) == 1:
            meta = obj["meta"]
            continue
        if _read_name(obj, t) or _read_level(obj, t) or _read_expr(obj, t):
            continue
        if _read_decl(obj, t, env):
            continue
        raise UnsupportedExport(f"line {lineno}: unrecognised item {sorted(obj)}")
    return env


def read_export_file(path) -> Environment:
    with open(path, "r", encoding="utf-8") as fh:
        return read_export(fh)

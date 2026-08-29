# ==============================================================================
# File: environment.py
# Description: The declarations a Lean environment is made of, and the store
#   they live in. The store is deliberately dumb: it holds what the export said
#   and answers lookups. Deciding whether any of it is true is the type
#   checker's job, and keeping the two apart is what stops a checker from
#   quietly trusting its own input.
# Usage: from src.kernel.environment import Environment, Declaration
# Tech Stack: Python 3.10+, standard library only
# ==============================================================================

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional

from .term import Expr, Name


@dataclass
class RecursorRule:
    """How a recursor reduces when it meets one particular constructor."""
    ctor: Name
    nfields: int
    rhs: Expr


@dataclass
class Declaration:
    """One constant. `kind` is axiom, def, thm, opaque, quot, inductive, ctor
    or recursor; the later fields are only meaningful for some of those."""
    kind: str
    name: Name
    level_params: tuple
    type: Expr
    value: Optional[Expr] = None

    # inductive
    num_params: int = 0
    num_indices: int = 0
    ctors: tuple = ()
    is_reflexive: bool = False

    # constructor
    induct: Optional[Name] = None
    cidx: int = 0
    num_fields: int = 0

    # recursor
    num_motives: int = 0
    num_minors: int = 0
    rules: tuple = ()
    k: bool = False

    is_unsafe: bool = False

    @property
    def has_value(self) -> bool:
        return self.value is not None and self.kind in ("def", "thm")


class Environment:
    """Declarations by name, in the order the export gave them."""

    def __init__(self):
        self._decls: dict = {}
        self.order: list = []

    def add(self, decl: Declaration) -> None:
        if decl.name in self._decls:
            raise KeyError(f"declaration already present: {decl.name}")
        self._decls[decl.name] = decl
        self.order.append(decl.name)

    def get(self, name: Name) -> Optional[Declaration]:
        return self._decls.get(name)

    def __contains__(self, name: Name) -> bool:
        return name in self._decls

    def __len__(self) -> int:
        return len(self._decls)

    def __iter__(self):
        for n in self.order:
            yield self._decls[n]

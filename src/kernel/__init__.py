# ==============================================================================
# File: __init__.py
# Description: The kernel: terms, the environment they live in, and the checker
#   that decides whether any of it is well typed. This is the only part of the
#   repository whose correctness the exit code depends on.
# Usage: from src.kernel import TypeChecker
# Tech Stack: Python 3.10+
# ==============================================================================

from .environment import Declaration, Environment, RecursorRule
from .term import Expr, Level, Name
from .typechecker import Declined, Rejected, TypeChecker

__all__ = ["Declaration", "Declined", "Environment", "Expr", "Level", "Name",
           "RecursorRule", "Rejected", "TypeChecker"]

# ==============================================================================
# File: errors.py
# Description: The two verdicts that are not acceptance. They live apart from
#   the checker because the inductive deriver and the type checker both raise
#   them and neither should have to import the other to do it.
# Usage: from src.kernel.errors import Declined, Rejected
# Tech Stack: Python 3.10+
# ==============================================================================


class Rejected(Exception):
    """The environment is not well typed, and here is why."""


class Declined(Exception):
    """This checker does not handle the input, and will not pretend to."""

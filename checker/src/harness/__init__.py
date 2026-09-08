# ==============================================================================
# File: __init__.py
# Description: The arena side of the repository: the entry point that turns a
#   checking run into one of the exit codes the benchmark reads. Nothing is
#   imported here, because `check_export` is run as `python -m`, and a package
#   that pulls the module in first has it loaded twice under two names.
# Usage: from src.harness.check_export import check_stream
# Tech Stack: Python 3.10+
# ==============================================================================

__all__ = ["check_export"]

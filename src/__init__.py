# ==============================================================================
# File: __init__.py
# Description: Package marker for the checker. Nothing is re-exported here on
#   purpose: the reader, the kernel and the harness are meant to be imported by
#   their own names, so it stays obvious which layer a call belongs to.
# Usage: import src
# Tech Stack: Python 3.10+
# ==============================================================================

__all__ = ["export_format", "harness", "kernel"]

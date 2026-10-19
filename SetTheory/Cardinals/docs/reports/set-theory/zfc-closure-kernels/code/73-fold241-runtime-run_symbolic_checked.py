"""Guarded entry point for the sealed, self-authored symbolic checker."""
import sys
if not __debug__ or sys.flags.optimize:
    raise RuntimeError('Symbolic proof checking requires enabled assertions; do not use -O or PYTHONOPTIMIZE.')
import symbolic_runtime
symbolic_runtime.main()

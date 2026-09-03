#!/usr/bin/env python3
"""Count the Lean source committed on the current branch: files, bytes, lines.

Only `.lean` files **committed** at the given revision (`HEAD` by default) are
counted, contents are read from the git object store rather than the working
tree, and submodules are excluded -- in particular the vendored Lean project
`lib/FormalizedFormalLogic-Foundation` contributes nothing.  See
`_source_stats.py` for the shared scope and line-accounting rules, which
`count_coq_code.py` uses identically so the two reports are comparable.

Results are split into hand-written versus machine-emitted code.  The
"generated" side is defined by the explicit, auditable glob list in
`GENERATED_PATTERNS` below: ProveIt's certificate trees are enormous (tens of
thousands of one-theorem `by decide` shards, plus flat coefficient tables) and
would otherwise drown out the human-authored corpus.  Pass `--flat` to skip
that split.

Usage:

    py scripts/count_lean_code.py                 # summary for HEAD
    py scripts/count_lean_code.py --rev main      # some other committed revision
    py scripts/count_lean_code.py --by-dir 1      # per-directory table, depth 1
    py scripts/count_lean_code.py --top 15        # largest individual files
    py scripts/count_lean_code.py --json          # machine-readable output
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import _source_stats as S  # noqa: E402

# Paths whose Lean files are emitted by a generator rather than typed by hand.
# Each pattern is matched with fnmatch against the repository-relative path.
GENERATED_PATTERNS = (
    "*/Certificates/*.lean",
    "*/ComputableDummitKernelCertificateTable*.lean",
    "*/LazardInvariantModularProductBridgeRow*.lean",
)

RULES = (("generated", GENERATED_PATTERNS),)


if __name__ == "__main__":
    raise SystemExit(
        S.run(
            language="Lean",
            extensions=(".lean",),
            syntax=S.LEAN,
            rules=RULES,
            description="Count committed Lean code (files, bytes, lines) in this repository.",
        )
    )

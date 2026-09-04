#!/usr/bin/env python3
"""Count the Rocq/Coq source committed on the current branch: files, bytes, lines.

Only `.v` files **committed** at the given revision (`HEAD` by default) are
counted, contents are read from the git object store rather than the working
tree, and submodules are excluded -- so the three Rocq/Coq libraries
registered as submodules under `lib/` (`Coq-Library-Undecidability-current`,
`Coq-Synthetic-Computability`, `MathComp-Abel`) contribute nothing.  See
`_source_stats.py` for the shared scope and line-accounting rules, which
`count_lean_code.py` uses identically so the two reports are comparable.

The `.v` corpus is split into repository-authored code and the *in-tree*
vendored snapshots under `lib/` (the imported Coq-BB5 developments and the
pinned Coq-Library-Undecidability copy), which are third-party code governed
by their own nested licenses.  Pass `--flat` to skip that split.

Comment handling differs from Lean: Rocq/Coq has no line-comment token, `(* *)`
comments nest, string literals are lexed inside comments, and `""` -- not a
backslash -- escapes a quote.  `_source_stats.COQ` encodes exactly that.

Usage:

    py scripts/count_coq_code.py                 # summary for HEAD
    py scripts/count_coq_code.py --rev main      # some other committed revision
    py scripts/count_coq_code.py --by-dir 1      # per-directory table, depth 1
    py scripts/count_coq_code.py --top 15        # largest individual files
    py scripts/count_coq_code.py --json          # machine-readable output
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import _source_stats as S  # noqa: E402

# In-tree third-party snapshots (submodules are already excluded upstream of
# this rule).  `lib/` is the repository's only vendored-code root.
VENDORED_PATTERNS = ("lib/*",)

RULES = (("vendored", VENDORED_PATTERNS),)


if __name__ == "__main__":
    raise SystemExit(
        S.run(
            language="Rocq/Coq",
            extensions=(".v",),
            syntax=S.COQ,
            rules=RULES,
            description="Count committed Rocq/Coq code (files, bytes, lines) in this repository.",
        )
    )

FROZEN CONCISEIPRA PYTHON SOURCE AUDIT
====================================

Repository: VladimirReshetnikov/ProveIt
Commit: 62396b06020f794fa6dc01b4025a6a5db9d4d28a
Root: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Research

All 90 package trees were retrieved without truncation. Their 5,825 Python
paths contain 1,380 distinct Git blobs. Every blob is included under
blobs/<git-sha>.py, with exact bytes checked against its Git object identity.
No repository source program was executed by this audit.

The empirical coordinate envelope among the existing standalone compact
checkers is 256 significant tokens / 276 AST nodes / 506 normalized bytes.
Three different programs attain these coordinates; no single existing
program with that joint score is asserted. This is a finite source-corpus
comparison, not a mathematical lower bound on all equivalent theories.

Reproduce with CPython 3.12.14:

    python3 reproduce_audit.py

The replay reads, hashes, parses and normalizes sources as data. It verifies
all 1,380 blob identities, every recorded metric, the three attaining
programs, and complete coverage of the below-envelope exclusion list.

METRIC
------
Remove actual docstrings from Module, FunctionDef, AsyncFunctionDef and
ClassDef bodies: only the first Expr(Constant(str)) is removed. Recurse
through all nested definitions. If removal empties a function or class,
insert Pass; leave an empty module empty. Apply ast.unparse, append one LF,
and reparse the normalized program. Count UTF-8 bytes, all ast.walk nodes,
and tokenizer items other than comments/layout/end markers.

This corrects an initial module-docstring-only pass. The correction changes
173 corpus measurements but none of the three frontier attainers. The
correction ledger is docstring_recomputation.json.

ELIGIBILITY
-----------
Small size alone does not make a file an eligible theorem checker.
subfrontier_exclusions.json explicitly classifies all 106 programs smaller
than at least one of the displayed envelope coordinates. They are report
builders, verification drivers, source generators, checksum utilities,
measurement programs, converters, or bounded diagnostics. Their reasons
for exclusion are given individually. In particular, source-generating
templates and drivers importing another checker do not receive the size of
that driver alone as a complete-checker score.

No claim is made that every remaining Python file is a sound or complete
theorem checker, or that the audit formally verifies existing mathematical
metatheorems. Compact certificate protocols and fully validated public
formula interfaces have different contracts and should be compared
separately when making implementation claims.

The frozen docs/incoming tree was independently checked and contains only
an empty .gitkeep file, so there is no unfiled proposal archive there.
The audit does not claim to measure non-Python implementations or source
text existing only inside compressed archives.

FINAL FILES
-----------
frontier.json                 Concise result, scope, attainers and limitations.
all_source_metrics.csv        Compact measurement ledger.
all_measured_blobs.json        Full measurements with every repository path.
all_py_blobs.json              Deduplicated source metadata.
all_py_inventory.json          Package-tree inventory.
subfrontier_exclusions.json    Explicit eligibility exclusions and reasons.
reproduce_audit.py             Non-executing source audit and replay.
blobs/                        Exact original repository source bytes.

# iPRA: adaptive seeds, finite quotients, and the current checker frontier

Prepared for Vladimir Reshetnikov, November 10, 2026.

## Status

**The requested smaller complete axiomatization has not been obtained.**
This is a research report with proved obstructions, a reproducible comparison
against the current drafts, and exact executable counterexamples to a proposed
checker simplification. It must not be described as a new checker below the
frontier or an absolute simplest axiomatization.

The mathematical contribution of this investigation is a broader obstruction
to computing a recursor's seed by finitely many adaptive queries to its own
update, followed by a stronger finite-dimensional quotient theorem. A language
whose numerical terms are bounded by unary functions of one input coordinate
cannot represent an infinite unital magma by a tuple of terms on any fixed
finite-dimensional domain, even modulo an arbitrary equivalence relation.
A composition of at most ceil(log2(d+1)) unit maps gives a finite set meeting
every equivalence class. The dependence bound is sharp. Relationally defined
operations remain outside the theorem.

The underlying class of almost unary functions is established in the
literature. The report attributes that fact and the earlier specific seed
obstructions. No literature-wide priority claim or proof-assistant verification
is made.

## Files

- `report.pdf`: typeset report with proofs, explicit inherited native rules,
  comparison tables, qualifications, and further research questions.
- `report.tex` and `theory/`: complete source for the new report.
- `reproduce.py`: offline reproduction of source metrics and scoped tests.
- `code/measure_sources.py`: normalization and gzip measurement.
- `code/unit_collapse.py`: the finite dependency algorithm and exhaustive
  small-system checks illustrating the quotient theorem.
- `tests/normalization/`: exact accepted proof of Q_y(0=0), a deliberately
  restricted checker that loses it, controls, provenance, and full logs.
- `reference/`: unchanged comparison checkers and gzip-9 files. These are
  inherited reference implementations, not new candidates.
- `reference/inherited_complete_presentation.tex`: an unchanged standalone
  source of the prior constructed-computation report, preserving its complete
  mathematical bridge and attribution. Its own earlier-snapshot measurements
  are historical; use the new report for the current comparison.
- `source_corpus/`: all 297 distinct Python sources in the inspected recursive
  archive corpus, named by SHA-256. They are included for offline measurement;
  the reproduction script parses them and does not execute them.
- `evidence/`: full provenance, archive/source inventories, metrics, review
  notes, and scoped validation outcomes.

## Reproduce

The recorded environment is CPython 3.12.14 with zlib 1.3.2.

```sh
python3 reproduce.py
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The Python reproduction uses only the standard library. Normalized source
counts depend on `ast.unparse`; gzip bytes can depend on the compression
runtime. A different environment can therefore require remeasurement rather
than reproducing byte-identical compressed streams.

The optional original `evidence/audit_frontier.py` is retained for provenance.
Unlike the offline reproduction above, it expects the original ZIP archives in
the repository layout described in its source. It is not the main entry point.

## Measurements

At ProveIt commit `0300a290bedee5019c974291850b798378438b2e`, the inspected
coordinate minima are 672 normalized bytes, 277 significant Python tokens,
and 311 AST nodes, achieved by different complete programs. The raw-source
minimum is 628 bytes. These are achieved upper bounds on an unknown optimum,
not proved lower bounds. The report counts ancillary and reference checkers,
includes parser and verdict code, and explains runtime-sensitive profiles.

Gzip is informational only. Every gzip measurement uses
`gzip.compress(source, compresslevel=9, mtime=0)`, including the gzip wrapper;
both raw and normalized source lengths are recorded. The 672-byte checker
compresses to 397 bytes. The smallest raw-source gzip stream among inspected
complete programs is 381 bytes, from a different, runtime-qualified profile.

## Attribution

The archived code and inherited report come from VladimirReshetnikov/ProveIt
at the pinned commit. Their original paths and hashes are preserved in
`evidence/`. The repository's MIT No Attribution license is reproduced in
`reference/LICENSE-ProveIt.txt`. The new report explicitly distinguishes its
proofs from inherited arithmetic and logical constructions.


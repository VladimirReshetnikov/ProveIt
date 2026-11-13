NEUTRAL RESOURCES IN CONCISE iPRA
================================
Prepared for Vladimir Reshetnikov, 13 November 2026.

RESULT
------
A new complete compact checker has 266 significant Python tokens,
299 AST nodes, and 460 normalized UTF-8 bytes. Its matched control has
267 / 298 / 461. The new dispatcher permits a zero image for a resource
whose logical reading is always the theorem 0=0. The same canonical
compiled certificate stacks continue to work.

Two further complete, fully validated programs lower the strict token
record from 306 to 304 and the strict AST record from 348 to 345:

  code/checker_tokens304.py     304 / 359 / 652
  code/checker_ast345.py        328 / 345 / 665
  code/checker_joint311.py      311 / 350 / 685

The last is an additional matched improvement, not a coordinate record.
Different programs attain different minima. All four new checkers use
the existing mathematical axiomatization and its full first-order iPRA
bi-interpretation; no arithmetic or logical axiom has been deleted.

IMPORTANT CLAIM BOUNDARY
-----------------------
This is a verified incremental improvement, not an absolute-minimality
theorem or a new mathematical axiom basis. No single new program is
below every compact coordinate minimum. The pooled compact envelope
changes from 239 / 255 / 461 to 239 / 255 / 460. The strict envelope
changes from 306 / 348 / 589 to 304 / 345 / 589. These are finite census
records, not proved complexity lower bounds.

The compact program has the SAME public-grammar promise as its matched
461-byte control. Its input alphabet is promised to consist of exact
integers/lists and its goal must be a canonical closed GUARDED Eq/D formula.
The compact program does not independently enforce these external promises.
Its soundness proof covers arbitrary auxiliary integer/list trees.

The validated programs check the entire parsed alphabet and the native
closed Eq/D goal themselves, including unused input entries. They have a
different numerical encoding and cannot share arbitrary compact certificates.

The new and old raw accepted certificate sets need not agree. The report
gives a deliberate new accepted certificate with a canonical theorem goal,
using a harmless noncanonical D(0=0) auxiliary that the control rejected.
The universal proofs, not the finite tests, establish logical soundness
and completeness. No new Lean/Rocq verification of Python execution is claimed.

READ
----
  ipra_neutral_modes.pdf       Complete new research report.
  ipra_neutral_modes.tex       Main LaTeX source; sections/ is required.
  sections/                   Theory, interpretations and new proofs.
  code/                       Four measured checkers and readable compact form.
  controls/                   Unchanged attributed comparison checkers.
  fixtures/                   Positive, negative and protocol-specific cases.
  evidence/                   Measurements, verification and provenance receipts.
  reference/upstream_article/  Exact pinned original article PDF and LaTeX sources.
  STATUS.json                 Machine-readable claim boundary.
  PROVENANCE.json             Commit, archive hashes and inherited contributions.
  MANIFEST.sha256             Integrity hashes of all other delivered files.

VERIFY
------
Use CPython 3.12.14 for the exact repository normalization:

  python3 reproduce.py

This first checks the original manifest, then remeasures the modules,
checks the supplied duplicate indexes, and runs 514 isolated executions:
180 compact and 334 strict, both normally and with -O. All expectations
passed during preparation. Regenerating receipts on another runtime can
change their metadata; check the original manifest BEFORE regeneration.
No verification step downloads anything or needs another proof checker.

Examples:

  python3 code/checker_bytes460.py < examples/compact_zero.json
  python3 code/checker_tokens304.py < examples/strict_three_field.json
  python3 code/checker_ast345.py < examples/strict_four_field.json

A successful run prints exactly ACCEPT followed by a line feed.
Completeness uses the same ideal finite-resource convention as the controls;
real memory and Python recursion limits can reject sufficiently large proofs.

BUILD THE PDF
-------------
With a normal TeX installation:

  latexmk -pdf -interaction=nonstopmode -halt-on-error ipra_neutral_modes.tex

Alternatively:

  python3 build_pdf.py

The latter uses only installed TeX files and can create a private format
when an installation lacks its format cache. It downloads nothing and
does not change system TeX configuration.

SOURCE SNAPSHOT
---------------
  https://github.com/VladimirReshetnikov/ProveIt
  7a7633980dbca7f599322a5e7f1e65fb1cddb7c8
  Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

All four incoming archives at this revision were inspected. Every included
upstream article source and its original PDF were checked against the pinned
Git blob hashes. The full arithmetic and logical bridge is inherited and
credited. The supplied upstream license is MIT No Attribution.
No GitHub repository file was changed.

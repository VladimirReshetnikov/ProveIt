CROSSED UNIQUENESS AND THE CONCISE iPRA FRONTIER
Prepared for Vladimir Reshetnikov, 12 November 2026

RESULT STATUS
=============
This archive does not establish the globally simplest axiomatization or one
complete checker below the full current complexity envelope.

It provides two distinct results:
(1) A mathematical primitive-basis fusion. On fully computationally normalized
    scalar terms, seeded crossed uniqueness derives equality transport and
    equation induction. The native six-rule calculus is bi-interpretable with
    full first-order iPRA by the written proof and the attributed existing
    scalar uniqueness and arithmetic bridges.
(2) A measured 502-byte compact checker of the EXISTING guarded calculus,
    reducing the audited 506-byte control. It has 269 tokens and 301 AST nodes;
    the separate existing 253-token and 275-AST minima are not improved.

The 502-byte program is not an implementation of the new uniqueness calculus.
The new calculus has a transparent strict reference checker, measured at
1909 tokens / 2087 AST nodes / 5618 normalized bytes. The strict companion of
the compact existing calculus is 1172 bytes versus its 1183-byte control.
There is no claim of a new Lean or Rocq verification.

READ FIRST
==========
ipra_crossed_uniqueness.pdf          Compiled research report with proofs.
ipra_crossed_uniqueness.tex          Modular main LaTeX source.
ipra_crossed_uniqueness_standalone.tex Self-contained LaTeX source.
CLAIMS.json                         Machine-readable exact claim boundaries.
sections/                           Main-paper LaTeX sections.

IMPLEMENTATIONS AND EVIDENCE
===========================
implementation/uniqueness/
  uniqueness_checker.py  Documented strict six-rule sequent checker.
  kernel_normalized.py   Complete docstring-free normalized executable,
                         corresponding to the 5618-byte measurement.
  build_certificates.py  Untrusted generator; expands numerical cases into
                         the actual primitive rules.
  certificates/*.json    Eight proofs, including common-source joining,
                         transitivity and nondefinitional iterator identities.
  verify.py             Eight positive and eleven targeted negative checks.
  VERIFICATION.json     Executed results.

implementation/compact/
  joint502.py           Compact promised-input checker of existing calculus.
  strict1172.py         Same public theorem set with grammar/alphabet validation.
  base506.py            Exact pinned upstream byte control.
  eager503.py, mode505.py Intermediate refinements.
  strict1183_control.py Matched validating control.
  reproduce.py          267 process checks plus source measurements.
  ARGUMENT.txt          Universal preservation/completeness arguments.
  results.json          Executed measurements and outcomes.
  current_corpus_match.json Current package hashes match the frozen census.

reference/
  scalar_uniqueness/    Attributed full scalar uniqueness bootstrap (.tex).
  scalar_bridge/        Attributed logical/arithmetic bi-interpretation sources.
  research_census/      All 1380 frozen Python blobs, 5825 path associations,
                       source metrics and classifications, with reproduction.
  incoming_*.py        Current token/AST/byte incoming profiles.

evidence/
  checker_review.md     Independent same-run review, not formal verification.
  mathematical_audit.md Detailed proof dependency audit.
  reproduction.json    Executed root reproduction report.
  latex_build.txt      Actual LaTeX build output.

REPRODUCE
=========
Verify the untouched download first:
    python3 verify_manifest.py

Replay new kernels and the complete frozen source census:
    python3 reproduce.py --census

Run one nontrivial equality certificate:
    python3 implementation/uniqueness/uniqueness_checker.py \
      < implementation/uniqueness/certificates/common_source_join.json

Run the input-validating compact companion:
    python3 implementation/compact/strict1172.py \
      < implementation/compact/fixtures/computation_zero_local.json

Rebuild the PDF:
    python3 build.py

Python scripts require only the standard library. The recorded metric runtime
is CPython 3.12.14; ast.unparse can change between Python releases.
PDF compilation requires a standard TeX Live distribution. build.py handles a
missing pdflatex format by making a temporary format from the installed files.

Reproduction regenerates result files. Rebuilding the PDF can change metadata
and binary hashes; MANIFEST.json verifies the supplied snapshot, not a rebuild.

CONTRACTS
=========
Compact: finite integer/list certificate plus a canonical closed guarded Eq/D
public goal. The compact source does not validate that promise; strict1172.py
does, and counts the validation in its module.

Uniqueness: exact JSON record keys scope, context, goal, proof. A theorem has
scope=0 and context=[]. Both f and h in a U proof bind one numerical template
variable. No term in h may refer to U's freshly introduced recurrence counter.
The checker validates scope before normalization and checks witness discharge.

Finite computation limits may reject large valid certificates. They never
constitute acceptance. General soundness and bi-interpretability are written
theorems, not consequences of finite regression tests.

SOURCE SNAPSHOT AND ATTRIBUTION
==============================
Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 6ffc49f55d355b548f7a8e1530570aee5de086b3
Project: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
Byte control Git blob: a0af7afb236b530eb30c63c5ab788151024271b7

The census originated in the incoming orbit report at the earlier commit
62396b06020f794fa6dc01b4025a6a5db9d4d28a. Every Research package tree hash is
unchanged at this report's snapshot. Incoming token/AST profiles are included
separately. All three incoming archives were inspected.

Inherited content retains its original license and attribution. Recursion
uniqueness is classical; the new elementary contribution is the arbitrary-seed,
crossed equality derivation. The byte contribution composes existing
refinements and is explicitly an implementation result.


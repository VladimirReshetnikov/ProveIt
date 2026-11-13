RETAINED PREMISES AND INFERRED MAJORS: SMALLER COMPLETE CHECKERS FOR iPRA
Prepared for Vladimir Reshetnikov, 12 November 2026

RESULT
======

At ProveIt commit 35a11d7434ab2a084d462af15702376190671294, the audited
reported compact-checker envelope is 256 significant tokens, 278 AST nodes,
and 516 normalized bytes. This package improves those coordinates to
253 tokens, 275 AST nodes, and 513 bytes, in THREE DIFFERENT PROGRAMS.
The coordinates must not be combined into a fictitious single checker.

This is an equivalent proof-checker presentation of the inherited scalar
iPRA theory. Its ordinary realization remains bi-interpretable and
equiconsistent with full first-order intuitionistic PRA, on whole numerical
domains with actual equality and identity numerical composites. The report
specifies all primitive axioms and rules, including the native logical
rules, and reproduces the inherited logical and arithmetic bridge.

The improvements are modest and measured. There is no absolute minimality
claim and no new Lean/Rocq verification. Existing reported sizes are
achieved upper bounds, not a proved universal lower bound.

START HERE
==========

ipra_retained_premises.pdf    Complete research report with attributed foundations.
ipra_retained_premises.tex    Flattened, self-contained LaTeX source.
paper.tex                    Modular authoring source.
code/readable_retained.py    Readable standalone expansion of the new R checker.
code/checker_retained_strict.py
                            Recommended executable interface: validates the
                            guarded public goal and all certificate field types.
evidence/metrics.json        Complete-module measurements, including controls.
evidence/validation.json     Detailed results and compiler statistics.
reference/PROVENANCE.json    Pinned upstream paths and exact Git blob hashes.
CLAIMS.json                 Scope of the mathematical and measurement claims.

PROGRAMS AND MEASUREMENTS
========================

Complete module                         Tokens   AST   Normalized bytes
Old token profile                         256    283         594
Old AST profile                           260    278         602
Old byte profile                          265    306         516
checker_inferred_tokens.py                 253    280         599
checker_inferred_ast.py                    257    275         607
checker_retained_bytes.py                  265    301         513

The G profiles reconstruct an elimination's required major when its target
template matches, then prove that major. They remove a redundant supplied-
major comparison. Their accepted raw certificate sets intentionally differ
from those of the old programs; the represented theorem set is unchanged.

The R byte profile uses an already retained equality or closure as its
major, recursively proves the source instance, and retains the target
instance. Automatic selection can intercept a computation. A fresh seed
alias U=I(0,u;v.r) repairs that collision using U=u, F(U), F(u).

Validated programs:
  checker_retained_strict.py: 421 tokens / 474 AST / 889 bytes, compared with
  407 / 459 / 921 for the existing guarded public-goal validator. The new
  validation contract is stronger: it checks all remaining certificate data
  is exact integer/list syntax, including any unused prefix.

  checker_native_validated.py: 347 / 400 / 700, compared with 358 / 413 / 788.
  This is an independent refinement of an unchanged native proof kernel.
  Its saving includes 65 bytes of diagnostic-path overhead. It is not a
  claim of fewer arithmetic or logical axioms, and it validates the public
  goal rather than all certificate field types.

CPython 3.12.14 is the reference measurement environment. Normalization is
ast.unparse(ast.parse(complete_module)) plus one newline. Runtime and Python
standard json library follow the repository convention. No producer,
normalizer, theorem database, or report-building code is imported by a
measured proof checker. Gzip measurements are informational.

INPUT CONTRACT
==============

A certificate is a JSON array. Its last item is the public goal. Remaining
four-field packets are consumed from right to left. Normal exit with exactly
ACCEPT and a newline is acceptance; exceptions reject. An unused prefix is
permitted, subject to the strict checker's type validation.

The compact profiles assume a canonical guarded Eq/D goal and integer/list
certificate trees. Their complete sorted auxiliary interpretation is given
in the report. Administrative truth arrays are not independent public
propositions. The 889-byte strict program validates these format conditions.

The token G profile uses global eigenparameter numbering and tests/global.
The AST G profile uses local numbering and tests/local. R uses LOCAL
numbering and tests/retained. R keeps both forward openings at the same
local parent floor. No unproved global R variant is delivered.

REPRODUCE
=========

From this directory, with Python 3.12:

  python3 reproduce.py

This checks 14 frozen Git blobs, regenerates the measurements, compiles 16
certificates while preserving their goals literally, and executes 692
standalone checker processes in ordinary and -O modes. The recorded run has
zero failed expected outcomes. The run includes 158 native-validator paired
comparisons. Finite tests support implementation review; the universal
equivalence statements are the written proofs, not conclusions from testing.

Example:

  python3 code/checker_retained_strict.py < tests/retained/computation_collision.json
  python3 support/compile_retained.py tests/local/transport_reflexivity_local.json proof.json
  python3 code/checker_retained_strict.py < proof.json

The translator is untrusted. It supports the packaged canonical old traces
and collision fixtures; no claim is made that it handles every arbitrary
aliased old certificate. The mathematical completeness proof constructs
compiler-normal proofs through the inherited guarded translation. It does
not rely on a blanket appendability theorem for every accepted raw trace.

BUILD THE REPORT
================

  python3 build.py

This expands the modular sources and code listings into the standalone .tex
and compiles it three times. It uses installed pdflatex assets. On a minimal
Debian image with TeX source assets but no generated format, it initializes
a local format and font map under build/texruntime without downloading
anything or modifying system-wide configuration. Ordinary complete TeX
installations use their normal format. The generated build/ directory is
not included in the distribution.

MATHEMATICAL CONTENT AND ATTRIBUTION
===================================

New: goal-directed major reconstruction; retained-major forward checking
with a closed-supply append invariant and fresh-seed collision repair;
an untrusted old-to-new certificate translator; exact measurements and
validation; a raw no-reflexivity variable-substitution obstruction.

Inherited: the scalar iterator basis, guarded public language, ordinary
intuitionistic logic macros, arithmetic bootstrap, source restriction,
sorted arity codec, and full two-composite bi-interpretation with iPRA.
The report reproduces those foundations with attribution. Frozen source
files retain their exact Git blob hashes. Their MIT No Attribution license
is included at reference/ProveIt_LICENSE.txt.

All complete-equivalence claims concern the canonical public theory and
its ordinary realization. No absolute checker-size optimum, no single
program attaining all three coordinate minima, no unrestricted compound
induction, and no new proof-assistant formalization are asserted.

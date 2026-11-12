REFLEXIVE-BASE INTRODUCTION FOR iPRA
Prepared for Vladimir Reshetnikov, 11 November 2026

START HERE
report.pdf       Complete mathematical report.
report.tex       Standalone source: no external inputs or figures.
code/checker.py  Complete selected proof checker.

MAIN RESULT
On the existing zero-normal scalar syntax, choose the progressive mode
of the single D-introduction exactly when its normalized zero instance
is literally r=r. Otherwise use its case mode:

  Gamma, B(t,eta) |- B(t,Sz)    ==>    Gamma |- D_(x,y) B

where eta=z for a reflexive zero instance and eta=0 otherwise.
The eigenvariable z is fresh for Gamma, t and all passive parameters.
Together with Hyp, successor computation, crossed one-term transport,
QE and DE, this gives six rules.

The written proof establishes exact equivalence with the current
seven-rule zero-normal kernel on all normal sequents. Composition with
the pinned normalization and native/iPRA bridges gives both interpretation
round trips, with whole numerical domains, actual equality and numerical
identity graph x=y. A raw seven-rule variant uses an asymmetric selector
gate and requires no normalization.

SIMPLICITY AND LIMITS
This is a modest mathematical rule-selection simplification.
Six rules were already attained by the witness-selected proposal.
The matched complete strict checker decreases from 3,095 to 3,084
normalized Python bytes and from 1,075 to 1,073 AST nodes.
The significant-token count remains 1,013.
Gzip level 9 increases from 977 to 981 bytes and is informational.

This is not a proof of absolute minimality and does not beat the separate
516-byte compact guarded codec. The smaller tagged implementation uses
validated formula arities to test reflexivity economically; the explicit
predicate version is supplied for readability.

VERIFICATION
The general equivalence is a written mathematical proof, supported by
constructive proof translators and independent review. There is no new
Lean or Rocq formalization.

Executed checks:
  13 substantive translation/control cases;
  16 malformed-input rejection cases;
  86 standalone executions, including Python -O;
  45 checks across selected, readable and source-normalized checkers.

The tests cover actual use of the induction hypothesis, nonreflexive bases,
nested binders, retained outer assumptions, both witness modes, and
false-to-true guard changes caused by substitution and zero normalization.
Finite execution checks supplement the structural proof; they do not
replace it.

REPRODUCE
Requires Python 3.10+; the measurement reference is CPython 3.12.14.
Only the standard library is used.

  python3 reproduce.py
  python3 code/checker.py < tests/certificates/reflexivity.json
  python3 build_report.py

The final command requires pdfLaTeX and standard TeX Live packages.
The standalone source also compiles directly:

  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

ACCEPT means exit status zero and exactly ACCEPT plus one newline.

PACKAGE CONTENTS
code/          Complete acceptance modules.
validation/    Untrusted proof translators, paired kernels, examples, tests.
tests/         A minimal runnable proof.
evidence/      Recomputed metrics, deterministic gzip files, verification,
               pinned source provenance and the exact checker diff.
reference/     Authenticated upstream controls, mathematical foundations,
               all 39 current ConciseIPRA Lean source modules and license.
front.tex, proof.tex, closing.tex  Editable report components.
build_report.py  Assemble and compile the standalone report.
measure.py       Complete-source measurement.
reproduce.py     All targeted verification and measurement.
CLAIMS.json      Exact scope of established results and limits.
SHA256SUMS.json   Delivered-file integrity ledger.

The included Lean modules are reference sources, not a standalone Lean
workspace. Build them in the pinned ProveIt project. They are not a newly
checked Lean proof of this proposal.

PROVENANCE
Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: d9383325b18d349b8bfdc54ef564c5784cc029ec
Directory: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
47 source files were authenticated against Git blob hashes.

The zero-normal syntax, scalar arithmetic bridge, one-term transport and
general guarded-introduction strategy are inherited. The cumulative
two-assumption rule already appears as Old DI in the inherited material
and is not claimed as new. The new contribution is the reflexive-base
guard, its structural treatment and raw extension.

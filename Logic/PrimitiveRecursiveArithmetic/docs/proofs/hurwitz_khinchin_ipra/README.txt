CONSTRUCTIVE HURWITZ AND KHINCHIN THEOREMS IN iPRA
Prepared for Vladimir Reshetnikov, 15 November 2026

START HERE
  hurwitz_khinchin_ipra.pdf   Complete human-readable research report.
  main.tex                   Main LaTeX source, with five section sources
                             and references.tex in the same directory.

MAIN MATHEMATICAL OUTPUTS
1. Sharp constructive Hurwitz approximation from a fixed primitive recursive
   rational name and quantitative rational-apartness modulus. The output
   is a strict exact rational certificate and a denominator above any B.
   Explicit finite-prefix extraction and golden-ratio optimality are proved.
2. Quantitative constructive Khinchin approximation. A convergence modulus
   gives rational null covers; monotonicity plus a unit-tail divergence
   modulus gives a primitive recursive finite coverage cutoff. The proof
   develops rational-point counting, overlap bounds, finite second moments,
   and repeated coverage in residual gaps, with all constants explicit.
3. Real-valued primitive recursive approximation functions are handled by
   rational lower/upper envelopes. Explicit null-test avoidance produces
   positive approximation witnesses without classical quantifier negation.

LOGICAL SCOPE
The internal assertions are first-order arithmetic schemata for fixed
primitive recursive definitions, with quantitative hypotheses supplied.
They do not quantify over arbitrary real functions inside iPRA and do not
assume a universal primitive recursive evaluator or an extracted modulus
from bare convergence/divergence. The report audits quantifier-free
induction and describes an actual route to embedded PRAAx derivations.

FORMALIZATION STATUS
  lean/Blueprint.lean          UNCOMPILED interfaces and explicit obligations.
  lean/FORMALIZATION_PLAN.txt   Detailed path to Lean and embedded iPRA.

This is not a completed Lean proof or an iPRA proof-checker certificate.
No Lean or Lake executable was available in the execution environment.
The scaffold contains no added axioms or sorry; its obligation records have
not been instantiated. Source inspection is distinct from a replayed build.

EXACT-ARITHMETIC ARTIFACTS
  code/finite_core.py     Arithmetic, certificates, interval operations.
  code/verify.py          Reproducible exact checks with a fixed random seed.
  code/verification.json  Generated detailed results, including exact fractions.

Run from this directory:
  python3 code/verify.py

Requires Python 3 with only its standard library. Checks are supplementary
implementation evidence, not proofs of the general mathematical theorem.
The general enormous residual-gap cutoff is specified but not executed.
The Hurwitz demo uses supplied continued-fraction digits; the general
modulus-based prefix extractor is described in the report, not implemented
by the demo.

REBUILD THE PDF
With a normal TeX Live or MiKTeX installation including the listed standard
packages, run three times:
  pdflatex -interaction=nonstopmode -halt-on-error \
    -jobname=hurwitz_khinchin_ipra main.tex
Alternatively run ./build.sh.

SOURCE PIN
ProveIt: 34c4c35edc8e648e57587c6faf3a5cfdd7879777
Lean: leanprover/lean4:v4.32.0
Mathlib revision: 81a5d257c8e410db227a6665ed08f64fea08e997
See sources/source_manifest.json and sources/repository_audit.txt.
No remote repository was modified.

INTEGRITY
SHA256SUMS.txt records hashes of the deliverable files (except itself).
The sources and code are included in full; network access is not required
to read the proof, rebuild the PDF with an installed TeX distribution, or
run the Python checks. Lean requires the pinned repository/mathlib setup.

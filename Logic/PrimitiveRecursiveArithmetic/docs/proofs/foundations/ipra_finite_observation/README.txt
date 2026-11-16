FINITE OBSERVATIONS AND UNIFORM CONSTRUCTIONS IN iPRA
Research package prepared for Vladimir Reshetnikov, November 15, 2026

START HERE
  ipra_finite_observation.pdf  Complete mathematical report.
  report.tex and tex/         Complete LaTeX source; keep them together.
  lean/FiniteObservation.lean Checked generic finite-table proofs.
  lean/Targets.lean           Type-checked specifications of further targets.
  provenance/sources.json    Pinned source paths and verified blob hashes.
  CLAIMS.json                 Claim-by-claim status and dependencies.

MAIN RESULTS
1. A finite observation compiler with separate evaluation and verification
   demands. It turns a variable-depth chain of one uniform table operation
   into a first-order primitive recursive table computation. The proof uses
   a fixed numerical challenge, backward horizon bounds, and Boolean finite
   invariants. Initial validity and a uniform local arithmetic proof are
   required; merely true or separately proved fixed-stage claims do not suffice.

2. Degree-uniform complete polynomial factorization, for each fixed PR
   coefficient evaluator. This extends the repository's fixed-degree
   factorization paragraph. The imported dependency is its finite rational
   descent lemma. The report proves the normalized root contract, explicit
   coefficient caps, deflator precision demand, backward table schedule,
   and finite coefficient telescoping estimate.

3. A derived local continuity modulus for the Bohr--Mollerup candidate.
   Positive rational multiplicative convexity implies ordinary convexity;
   two endpoint estimates give Lipschitz constant M/delta on an interior
   rational interval. This removes the candidate modulus as independent
   input for the canonical extension of the rational presentation.

4. Finite-net infimum names and coherent minimizers from quantitative
   uniqueness, including a complete strong-convexity instance. The infimum
   value needs no uniqueness assumption; the coherent-point theorem here
   additionally assumes quantitative uniqueness.

5. An elementary sharp superelliptic section bound. For y^r=f(x), with
   degree(f)=m>r*s, each proper subspace contains images of at most m distinct
   points under (1,x,...,x^s,y). A supplied tuple-local M-subspace cover gives
   cardinality <=m*M. For quintics y^2=f_5(x), the bound per section is five.
   The theorem that would produce covers in the general Siegel/Faltings
   application is NOT supplied by this package.

FORMALIZATION STATUS
  FiniteObservation.lean compiled under Lean 4.32.0. Its proved theorems
  include compiled_correct, allBelow_iff, finite_safety, and descent_fuel.
  Axiom printouts contain propext and Quot.sound; no Classical.choice or
  sorryAx appears in those outputs.

  Targets.lean also compiled under Lean 4.32.0. Its Spec structures and
  Goal propositions are typed definitions / pending proof obligations.
  Their type checking is not a proof of the analytic or algebraic results.

  No full deep object-language Prf PRAAx derivation of the new mathematical
  applications is claimed. Section 8 of the report explains how to build
  those derivations from the inspected ConciseIPRA backend, with all major
  data representations, finite contracts, numerical schedules, and proof
  milestones stated. Ambient Lean functions are not automatically PR.

REPRODUCTION
  ./build_pdf.sh
  python3 code/finite_observations.py
  python3 code/analysis_exact_checks.py
  python3 code/finite_curve_sections.py
  cd lean && ./check.sh

  Use Lean 4.32.0 for the supplied Lean files. Set LEAN_BIN to the desired
  executable if it is not named lean on PATH. The source uses Std only.
  The full repository integration will use the pinned Mathlib/ConciseIPRA
  environment. No dependency is fetched by the supplied check script.

  LaTeX requires standard AMS, Latin Modern, geometry, microtype, listings,
  enumitem, booktabs, xurl, hyperref, and fancyhdr packages. The build script
  has a fallback for the incomplete format cache present in the preparation
  environment. It does not use shell escape or need network access.

VALIDATION LIMITS
  The Python outputs are exact implementation/example checks, not an iPRA
  proof checker. The degree-1 through degree-4 FTA run checks numerical
  budgets only; the huge full descent algorithm was not executed. All
  relevant evidence files retain this scope distinction.

  The repository inventory was inspected at commit
  94000996e69ab0c527393a1d02a4a037a4eb0493.
  Selected source files were checked against their current Git blob hashes.
  This is not a blanket correctness audit of the 48 repository packets.

CONTENTS
  tex/          Nine report sections plus bibliography.
  lean/         Checked generic kernel, typed targets, status notes, toolchain.
  code/         Three standard-library-only exact example implementations.
  evidence/     Executed checks, Lean output, PDF QA, and build status.
  provenance/   Source manifest and exact obstacle locations.
  INTEGRATION.txt  Suggested repository placement and milestone order.
  SHA256SUMS       Checksums of the delivered files, excluding this manifest.

BOUNDARIES RETAINED
  No primitive recursive universal evaluator for arbitrary PR program codes.
  No exact Puiseux branch data from arbitrary Cauchy names.
  No conversion of mere nonzero to quantitative apartness.
  No general conversion of metastability to a Cauchy rate.
  No general conversion of cardinality plus pairwise gaps to a height cutoff.
  No claimed solution of general Siegel, Faltings, Chebotarev, effective
  Siegel--Walfisz, Bombieri--Vinogradov, or advanced CLT obstacles by coding.

PRIME DISTRIBUTION IN INTUITIONISTIC PRIMITIVE RECURSIVE ARITHMETIC
Research proof package — 15 November 2026

READ THIS FIRST

This is a PARTIAL resolution of the request for five full proofs in iPRA.
It contains complete human arguments for Dirichlet infinitude (with an
explicit primitive recursive bound and reciprocal-sum divergence) and
sharp Brun–Titchmarsh (constant 2 for every rational x > q), together with
a detailed finite arithmetic realization. It does not contain complete
iPRA proofs of Chebotarev, Siegel–Walfisz, or Bombieri–Vinogradov.

The latter three chapters supply exact targets, proved finite/conditional
reductions, and a precise account of missing inputs. Their gaps are not
asserted to be impossibility or nonprovability results.

No completed, kernel-checked Lean proof or embedded Prf PRAAx object is
claimed for any theorem. The Lean files are an uncompiled definition and
development outline. This distinction appears on the report’s title page,
in the status table, and in verification/STATUS.json.

START HERE

  prime_distribution_ipra.pdf   Complete human-readable report
  paper/main.tex               Main LaTeX source
  paper/sections/               All mathematical chapters
  lean/Targets.lean            Executable finite definitions and Prop targets
  lean/ObjectBridge.lean       Conditional bridge to the actual ProveIt calculus
  lean/ROADMAP.txt             Dependency order and formal endpoints
  code/                       Exact arithmetic diagnostics/certificates
  verification/               Executed outputs, status, review records and build QA
  provenance/sources.json      Source URLs and inspected repository-file hashes
  SHA256SUMS                   Integrity manifest

MAIN PROVED STATEMENTS

1. Dirichlet. For q >= 1, gcd(a,q)=1 and B >= 0, set

     D = 2^25 (q+1)^2,
     C = 1 + 16 q^2 2^D,
     T = 8q(B+C+q+4),
     Y = 2^(T 2^T).

   Then the sum of 1/p over primes p <= Y congruent to a modulo q exceeds
   B+1. Hence a prime B < p <= Y exists and bounded search supplies it.
   The literal arithmetic endpoint multiplies the sum by Y!.

   The bound is intentionally enormous. DO NOT attempt to evaluate Y or
   Y! in the scripts or Lean. The finite diagnostics never do so.

2. Sharp Brun–Titchmarsh. For rational x > q >= 1 and gcd(a,q)=1,

     pi(x;q,a) <= 2x / (phi(q) log(x/q)).

   The proof includes a weighted cosecant inequality proved through a
   finite rational grid, a weighted large sieve, explicit denominator
   bounds, and overlapping small/large ranges. Exact rational certificates
   verify the finite numerical side conditions. The report also proves a
   simpler rational Selberg bound and an explicit (2+1/k) consequence.

WHAT REMAINS OPEN IN THIS PACKAGE

Chebotarev: certification of the complete number-field algebra interface,
then primitive recursive field-dependent parameters and embedded proofs
of the effective prime-ideal estimates. A full numerical passage from
supplied estimates to a density modulus is proved.

Siegel–Walfisz: the full uniform exponential estimate and its positive
constructive parameter witnesses. The exceptional-real-zero contribution
and the strength of the needed conductor dependence are displayed.

Bombieri–Vinogradov: the full mean-value theorem, including its small-
conductor range. Finite Vaughan and Gram identities and a witness-preserving
reduction to logarithmic-power Siegel–Walfisz estimates are proved.
Effective restricted-modulus or sifting variants are not substituted for
the full requested theorem.

REPRODUCING THE FINITE CHECKS

Requires Python 3.10 or later. No third-party Python dependency is needed.
From this package directory:

  python3 code/dirichlet_checks.py
  python3 code/finite_sieve.py --self-check
  python3 code/finite_swbv.py
  python3 code/sharp_bt_certificates.py

All four print JSON. The saved results are in verification/. Comparisons
use Python integers and fractions.Fraction. These programs are finite
mathematical diagnostics, not universal-theorem or iPRA proof checkers.
The sharp-BT finite side-condition cases are genuine ingredients of its
human proof; they are explicitly bounded and reproducible.

BUILDING THE PDF

A standard TeX Live installation with Latin Modern and the ordinary
AMS, hyperref, listings, microtype and geometry packages suffices.
There are no external graphics or bibliography-generation dependencies.
Run:

  bash build.sh

Or run pdflatex on paper/main.tex repeatedly until cross-references settle.
The script writes prime_distribution_ipra.pdf and refreshes finite-check
outputs. For a pristine manifest comparison, check SHA256SUMS BEFORE
rebuilding: a fresh PDF may have different metadata and thus a new hash.

LEAN AND REPOSITORY REUSE

Inspected repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned commit: 7eeb3c0e821594d5d5ebcfbaf4bdba64819e3502
Declared toolchain: leanprover/lean4:v4.32.0

Targets.lean imports Mathlib. ObjectBridge.lean imports
ConciseIPRA.NativeBiInterpretation and is intended for an environment where
that library is on Lean’s import path. The supplied bridge is conditional
on an existing object-language derivation; it does not construct one.
No Lean/Lake executable was available in the authoring environment, so
these files have not been compiled. The inspected repository’s human
analytic packages are not treated as already checked analytic axioms.

REVIEW AND PROVENANCE

The report records primary literature, author-hosted papers/course notes,
and actual repository interfaces. Independent mathematical reviews checked
the central Dirichlet coefficient argument, finite approximation repairs,
sharp weighted-sieve proof, and SW/BV targets. Such review is not Lean kernel
verification. Review records preserve corrections and their disposition.
No upstream repository files were changed.

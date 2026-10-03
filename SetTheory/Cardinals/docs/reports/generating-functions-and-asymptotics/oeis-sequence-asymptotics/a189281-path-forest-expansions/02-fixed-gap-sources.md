# Source audit and provenance

Audit date: October 1, 2026. These sources support definitions, the status of
previous work, and input data. The new derivations are given in the article.
A missing proof in an OEIS entry is not by itself a guarantee that no published
proof exists; the report does not claim independently established priority.

## OEIS

**A189281** — https://oeis.org/A189281/internal

Defines a(2,2)(n), still labels the particular displayed recurrence conjectural,
and associates correction coefficients through n^(-10) with that recurrence.
The entry records independent verification of the recurrence through n=300.
The article proves the expansion without relying on the recurrence.

**A110128** — https://oeis.org/A110128/internal

Defines b(2,2)(n), cites Tauraso for the classical result, and displays coefficients
through n^(-10) associated with a guessed recurrence. Those coefficients are
reproduced by the independent finite-defect calculation.

**A189281 b-file** — https://oeis.org/A189281/b189281.txt

Public exact values copied into the verification script: n=0,...,26 and selected
n=20,40,80,120. The script independently regenerates n=0,...,26 and n=40.
The n=80 and n=120 values are external inputs to the numerical checks.
The OEIS entry credits Rintaro Matsuo for the extended table, with earlier ranges
credited to Vaclav Kotesovec and Christoph Koutschan. This package contains only
the selected input integers, not a republished copy of the full OEIS entry.

## Primary literature

**Roberto Tauraso (2006)** — The Dinner Table Problem: The Rectangular Case,
Integers 6, A11; https://arxiv.org/abs/math/0507293

Used for attribution of the equal-gap absolute-difference leading limit and
first correction. Theorem 4.1 is the relevant reference. Its PDF page 8 was
visually inspected. No result from it is needed to replace a missing proof in
our independent argument.

**George Spahn and Doron Zeilberger (2022)** — Counting Permutations Where The
Difference Between Entries Located r Places Apart Can never be s (For any given
positive integers r and s); https://arxiv.org/abs/2211.02550v3

Provides the matching-tilings inclusion-exclusion formulas. Our exact-moment
formula is the same underlying combinatorics with a retained pgf variable.
The original formulas, including the orientation factor, are credited rather
than claimed as new. PDF page 6 was visually inspected.

**Manuel Kauers and Christoph Koutschan (2022)** — Guessing with Little Data;
https://arxiv.org/abs/2202.07966

Background for the recurrence-guessing problem; no guessed operator is used
as a proof dependency.

**Jaideep Sai Padhi (2026)** — Solutions to Five Challenge Problems in Enumerative
and Algorithmic Combinatorics, with an Account of the Human–Machine Methodology
Employed; https://arxiv.org/abs/2608.11290v2

This August 2026 preprint claims general holonomicity in section 5, while its
section 6 on the specific a(2,2) operator is explicitly partial. Included to
avoid falsely presenting general holonomicity as an untouched problem.
The present paper does not rely on or certify the preprint's proofs.

**NIST DLMF** — https://dlmf.nist.gov/5.11 and https://dlmf.nist.gov/4.13

Standard gamma asymptotics and Lambert-W definitions used in the inversion.

## ProveIt context

Repository: https://github.com/VladimirReshetnikov/ProveIt

The recursive main-tree response during the audit identified commit
291fbe6bb4477e0cb2131f1e041b12a9abe363fd. The README was inspected, and a GitHub
repository code search for A189281 returned total_count=0 and
incomplete_results=false. This is a focused duplication check, not a guarantee
that every archived or binary artifact was reviewed. The mathematical argument
is self-contained and does not assume any unpublished theorem in ProveIt.

## What the computations do not establish

Finite tests do not prove the conjectured target recurrence, prove all-order
integrality, establish global novelty, or provide a formal proof-assistant
certificate. The article supplies separate all-n proofs for the stable-profile,
asymptotic, and boundary-universality results. Numerical error tables are not
interval certificates and are not advertised as such.

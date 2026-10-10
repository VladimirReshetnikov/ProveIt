ODD-INNER SHUFFLE DIAGONALIZATION AND GAUSSIAN CANDIDATES
======================================================

Scope and status
----------------
The article and sections/05_shuffle_and_identities.tex contain the
mathematical definitions and complete proofs.
The integral matrix equivalence

    U M V = diag(1, 3, ..., 2m-1)

is proved for every positive integer m. The associated determinant,
cokernel, characteristic-dependent rank, and optimal inverse-denominator
statements are theorems. They concern a specified formal shuffle quotient;
they do not assert independence of numerical polylogarithm periods.

The weight-eleven S10 identity and the optional weight-thirteen S12
identity are CONJECTURES. For each retained frozen vector the accompanying
integer/rational computation proves that the normalized residual lies
strictly between -10^-650 and 10^-650. Each delivered residual interval
contains zero. These facts prove finite proximity, not equality.

A weaker, discarded S12 vector is rigorously rejected: its unnormalized
integer residual lies strictly between -2191/10^277 and -2190/10^277.
The rejected and retained vectors are separate records in the canonical
gaussian_candidates.json file.

The existing S6 conjecture has not been proved by this work. A larger
weight-seven word presentation was scoped but no new completed full-matrix
rank computation or S6 certificate is claimed.

Portable replay
---------------
Run the following commands from the package root. The Gaussian programs
remain together with gaussian_candidates.json in code/gaussian/. The
independent matrix verifier is in code/shuffle/. Programs locate their
data and output relative to their own directories and do not require
the source checkout, network access, or non-bundled research files.

1. Exact rational proximity and rigorous rejection, Python >= 3.11,
   standard library only:

       python3 code/gaussian/verify_gaussian_proximity.py --s12

   Omitting --s12 checks only S10. The default is 2200 Euler terms,
   600 terms in each Machin arctangent series, and 800 logarithm terms.
   The full replay writes gaussian_proximity_certificate.json and takes
   about 45 seconds on the original environment. All interval endpoints
   are serialized as exact [numerator, denominator] decimal-string pairs.
   Every reported 10^-650 proximity bound refers to the integer dot
   product divided by the coefficient of S_p. The certificate also
   records the unnormalized rejected S12 residual explicitly.

2. Exact finite checks of the general matrix construction, using SymPy:

       python3 code/shuffle/verify_odd_inner.py

   This checks the displayed factorization and unimodular matrices,
   determinant, Smith form, and optimal inverse denominators for m=1,...,20;
   it writes odd_inner_certificate.json. It also checks the short exact
   weight-eleven shuffle identity. These finite checks supplement the
   all-m proof in the notes; they do not replace it.

3. Optional independent numerical representation audit, using mpmath:

       python3 code/gaussian/audit_s10.py 120

   This uses Mellin quadrature instead of finite Euler sums and writes
   s10_mellin_audit.json. The saved run used 120 working decimal digits
   and gave a normalized residual approximately 3.49e-121. No rigorous
   quadrature error bound is claimed. The exact rational verifier in
   step 1 is the authority for the finite proximity statement.

4. Optional exploratory integer-relation search, using mpmath:

       python3 code/gaussian/search_s10.py 10
       python3 code/gaussian/search_s10.py 12

   This writes s10_search_replay.json or s12_search_replay.json. The script
   computes the values at 550 digits from 1600 finite Euler terms, searches
   initially at 300 digits, rejects a candidate that fails the retained-
   precision numerical guard, and then searches at 440 digits if needed.
   Search output is exploratory and cannot prove equality or independence.

   The archived s10_search.json and s12_search.json preserve the original
   discovery history. In the historical s12_search.json, the top-level
   frozen_vector is the subsequently REJECTED first result, while the
   retained vector is under extended_search. This historical naming is
   not an authority for the final candidate: gaussian_candidates.json
   is the explicit, compact canonical input to all verification scripts.

Recorded environment
--------------------
Python 3.12.14; SymPy 1.14.0; mpmath 1.3.0.
The exact rational proximity verifier uses neither SymPy nor mpmath.

Reference source snapshot
-------------------------
VladimirReshetnikov/ProveIt commit
3447bc59b78d138a7f0d536b66ac6e5cc5d5e49f.
The notes distinguish results already in that snapshot from additions.
The determinant is connected to Zagier's matrix and published subsequent
work; no worldwide novelty claim is made for that determinant formula.

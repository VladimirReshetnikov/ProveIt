# Claim status and logical scope

## Proof claims supplied in the article

1. Theorem 2.1: complete root-of-unity minimal-denominator classification for
   every k >= 1 and every primitive root of order ell >= 3. The integer rule
   includes empty residue classes and complete disappearance of a factor.
2. Theorem 5.1: explicit first centered subleading coefficient of a canonical
   confluent rectangular-Schur spectral polynomial with arbitrary cluster
   multiplicities and distinct nonzero nodes, when its degree is positive.
3. Theorem 7.1: exact four-residue product formulas at t = +/-i for k=4m+1,
   m >= 1.
4. Theorem 8.1: the exceptional phase has degree 2m^2-5 for m >= 2, with
   explicit nonzero leading coefficient; it vanishes for m=1.
5. Corollaries 9.1--9.4: all complex parameters, compact fourth-root forms,
   least quasipolynomial period, and fixed-order quadratic recurrence growth.

## Explicit inputs and already-existing mathematics

- The normalized Hankel--Schur identity (article equation 1.4) is imported
  from Part II, Theorem 12.1 of the pinned ProveIt report. Its consequences
  here are not presented as a proof-assistant verification of that input.
- Bialternants, Schur complementation, the confluent leading coefficient,
  and the generic/real recurrence classifications are prior mathematics or
  prior repository results. They are credited and rederived where needed.
- The odd-shift Hankel block elimination is rederived in Section 7.
- The beta determinant and normalization calculations used at fourth roots
  are proved in Appendix A by an elementary rational determinant identity.

## What was actually checked computationally

The delivered run is recorded in `data/verification.json` and its log.
All checks passed using exact arithmetic:

- 54 canonical Cigler modes at k=2..7 and t=2,3;
- 22 additional modes with other cluster multiplicities;
- 80 fourth-root values over Q(i), m=1..4 and n=0..19;
- symbolic triangular power-sum differences and Newton identities, with m
  left symbolic (not merely evaluated at finitely many m);
- 144 normalized-Hankel/Schur comparisons, k=1..8, n=0..5, t=2,-2,i;
- 240 finite-field recurrence reconstructions, k=2..17 and ell=3..17.

The finite-field tests concern specialized finite prefixes. They do not
independently prove a characteristic-zero identity or an infinite-range
statement. No theorem is justified solely by extrapolation from these tests.

## Not claimed

- Lean, Rocq, or other proof-assistant verification of the new theorems.
- An independent referee's endorsement or exhaustive worldwide priority.
- Resolution of all assertions of Cigler's Conjectures 17 or 18.
- The same minimal denominator for the unnormalized D_k(n;t): its extra
  quadratic phase must be handled separately.
- A classification for a middle cluster of multiplicity greater than one,
  uniform detuning asymptotics, or an expanded cyclotomic numerator formula.

The work resolves the precise cyclotomic gap in the inspected repository
source; the mathematical presentation and the accompanying finite evidence
are deliberately distinguished.

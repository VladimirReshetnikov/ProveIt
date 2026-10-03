# An exact four-mass obstruction to timed semilinearity

This is a counterexample to extending the mass-three timed conclusion. It is not a counterexample to mass-four untimed decidability.

## Rule

Alphabet {0,u,R,L}, weights w(0)=0, w(u)=1 and w(R)=w(L)=2. Thus u is the unique unit label, and the vacuum is the only zero-weight label. R and L are different labels with the same weight, so this example is not an ordinary numerical-state NCCA.

A site x carrying R or L is an eligible heavy center if no other R/L center occurs within distance 4. Apply the following rewrites at every eligible center in parallel; all other sites stay unchanged:

- R at x and empty x+1: move R to x+1.
- R at x, u at x+1, and empty x+2: replace R by L at x, erase u at x+1 and write u at x+2.
- L at x and empty x-1: move L to x-1.
- L at x and u at x-1: replace L by R at x, leaving the unit unchanged.

If none applies, the center stays unchanged.

Eligible centers have separation at least 5. Their rewrite supports lie in [x-2,x+2], so are disjoint. No eligible rewrite can touch another heavy center, because that would violate the distance-4 guard. Every rewrite preserves weight; hence every finite-support configuration preserves weight exactly. To determine output at a site y, only centers within distance2 can affect it, and each eligibility test examines distance4 around that center. Radius6 therefore suffices. The all-vacuum configuration is fixed, as is every isolated unit.

## Exact orbit and non-semilinear hit set

Start from u at0, R at1, and u at d, with d>=3. The total mass is four.

Whenever the orbit has u at0, R at1, and u at D, the head travels right to D-1 in D-2 steps, reverses and pushes the right marker to D+1 in one step, travels left to1 in D-2 steps, then reverses to R in one step. The next return is therefore after 2D-2 steps, with D increased by1.

The anchored two-site pattern (u,R) at sites0,1 occurs exactly at

    t_k = sum_{i=0}^{k-1} (2(d+i)-2)
        = k^2 + (2d-3)k,       k>=0.

There are no additional hits: between successive returns R either moves strictly right from1, or the head is L. Successive hit gaps are 2k+2d-2, unbounded. Every infinite eventually periodic subset of the nonnegative integers has bounded gaps beyond a finite prefix. This hit set is therefore not eventually periodic and is not Presburger-definable.

Thus even the per-input timed occurrence-set conclusion of the mass-three theorem fails at mass four in the unique-unit weighted class. Uniform timed Presburger definability fails a fortiori.

## Executable checks

Run `python test_expanding_shuttle.py` with Python3. It uses only the standard library. Recorded results:

- 65,536 exhaustive width-eight conservation checks
- 202,300 direct orbit steps at d=3,...,19
- 1,717 exact formula-predicted return times (k=0,...,100)
- 10,000 randomized radius-six locality and translation checks

These tests supplement the exact disjoint-rewrite and orbit proofs; they are not exhaustive validation of the general mass-four theorem. See shuttle-test-results.json for the machine-readable ledger.

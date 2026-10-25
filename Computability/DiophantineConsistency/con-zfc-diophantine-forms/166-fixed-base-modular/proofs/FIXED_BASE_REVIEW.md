# Independent review of fixed-growth arithmetic

## Reviewed objects

- `code/build_fixed_base.py`, including the selected
  `--linear-beta` source alteration.
- `proofs/FIXED_BASE_PROOF.md`, all eight sections.
- `stages/fixed_base/raw_source.json`, exact
  hash recorded by `verification/fixed_source.json`.
- The inherited Factorial-Free Binomial CRT report's lcm-bound and
  generalized CRT statements, its arithmetic source proof, and its
  original square-radix completion.

This is an independent AI-assisted mathematical and source-code review,
not external human peer review or an end-to-end formal-assistant build.

## Mathematical assessment

The selected argument is sound relative to its explicitly retained Pell,
generalized binomial CRT, local-rule, and C222/refutation interfaces.

1. The lcm induction is valid. The quotient of consecutive half-scale
   lcms divides the central binomial because every new prime-power level
   contributes one to its valuation. The odd case uses the two equal
   central binomial coefficients and hence the necessary factor of two.
   It proves `lcm(1,...,t)^2 <= 16^t` without an asymptotic estimate.
2. The first fixed-base power gives `R=16^t`, while `q=6z+3` excludes
   zero and both unit bases. Thus the signed-power theorem authenticates
   every numerator exponent and gives nonnegative actual CRT representatives.
3. The raw index congruence excludes `B=0` before binomial decoding.
   The exact denominator request at exponent `y+1` gives `y>=-1`.
   Since `y=RB(2v+1)^2` and `R>1`, a negative B would give `y<-1`.
   This acyclic argument proves `B>0` directly, and then proves `q>0`.
4. The surviving denominator ratio forces `x>=t+1`, ruling out the
   exceptional beta-code values zero and one. The last beta endpoint
   gives `x>=2+(t+1)y`, and `y>=RB>B` makes the first endpoint a genuine
   initial remainder `B+1`.
5. Adding `2(R+t)` to the radix multiplier supplies the required uniform
   binomial coefficient bound before B is authenticated. Normalized
   remainder uniqueness and a strict digit separation bound recover
   `B=binom(R+t,t)`.
6. This same B exceeds `(t+1)^t`, so the unchanged polynomial-evaluation
   proof recovers Horn-label multiplicities. Every decoded local row is
   bounded by the inherited majorant with F replaced by B.
7. Completeness requires the factor R in beta spacing. Its 2-adic
   valuation is `4t`, and the square of an odd multiple of the odd part
   of t! supplies all remaining divisibility. The binomial B is odd.
   The mod-6 lift of the dominant representative makes BH an odd
   multiple of three while preserving the even semantic anchor.
8. Enlarging the dominant representative's allowed upper bound from
   `4N^2` to `8N^2` does not invalidate any bound: its lower bound is
   unchanged, its quadratic derived label dominates every other index,
   and the self-sized radix uses its actual enlarged value.

The original proposed beta formula without R was rejected during
development: B is odd, so it cannot supply the necessary power of two
for a universal beta-CRT completion. The selected source contains R.
The intermediate squared-B formula was simplified to linear B only
after proving sign recovery from the existing exponent `y+1`.

## Literal source audit

`check_fixed_growth_source.py` is separately written and imports no
producer, factorizer, or eliminator. It reconstructs all 383 raw residuals
from the authenticated parent by an independent exact polynomial recipe.
It checks the 18 altered rows, the one removed growth-base row, all 18
power interfaces, and the complete square frame with 37 distinct atoms.
It also checks every retained or renamed coordinate and degree at most two.
Normal and optimized Python both pass.

The final affine/radix companion and the later modular-numerator
alteration have separate certificates and proofs. This review does not
claim to cover an uninspected successor merely because it uses this source.

# Independent review of symmetric digit budgets and the odd-square radix

Review performed by a separately tasked AI-assisted research agent on
25 October 2026. This describes an independent check within the present
workflow, not outside human refereeing.

**Conclusion:** the new ordinary argument in `PROOF.md` is sound relative
to its expressly retained direct-C222 arithmetic and logical calibration.
No mathematical defect was found in the pooled remainder replacement, the
adjacent-scale merger, or the odd-square restriction and its completeness
construction. The independent literal checks also pass.

## Materials actually examined

- The complete new `PROOF.md`, including all three endpoint constructions.
- The literal inherited guarded source and its source certificate.
- The actual `STRICT_BUDGET_PROOF.md` and `ORIENTATION_FIRST_PROOF.md` in
  the pinned incoming cofinal-anchors archive, including the initial
  orientation theorem, the negative-exponent exclusion, the strict endpoint
  recovery, the zero-representative correction, and the parity-selective
  completeness schedule.
- The new raw source graphs for `four_pools`, `three_pools`, and
  `odd_three_pools`.
- Every final residual and every expanded coefficient in the corresponding
  three centered endpoints.

The review does not claim a fresh end-to-end formal replay of the inherited
C222/ZF/ZFC equivalences. It checks the new unbounded mathematics and the
literal changed sources against the stated inherited boundary.

## Mathematical audit

1. **The ternary completion is genuinely universal.** For every nonnegative
   integer N, the three-square theorem applies to `4N+1`. Exactly one square
   in such a representation is odd; the other two are even. Thus
   `N=u^2+v^2+w(w+1)`. Conversely each summand is nonnegative for every
   integer input, including negative w. The new budget row therefore says
   exactly that its integer slack is nonnegative.

2. **The removed signs are used only after power recovery.** The old
   orientation-first and strict-budget proofs orient both coordinates of
   every principal Pell pair using the signed anchor and the common frame.
   The deleted eleven product signs are not premises of those steps. In
   particular the apparent binomial expressions in the proof are semantic
   descriptions of exact recovered power outputs, not extra operations in
   the new polynomial.

3. **The radix margin does not use the factorial fixed point prematurely.**
   From the raw ceiling and endpoint data one has `F>=1`, `B>=2`,
   `V0=(F^2+1)^t`, `y=V0(V0-1)`, and `x>=2+(t+1)y`. Since `t>=16`, both
   `x>=ell*t+4` and `x>=t(t+1)+4` follow, for `ell=2^22`. The ordinary and
   factorial upper-index coefficient estimates then follow directly.
   The new derived-label estimate uses `(2H0)^ell`, not the stronger later
   `H0^ell` estimate that requires a nonzero encoded index. Consequently the
   boundary case `H0=1` is covered before factorial semantics.

4. **Signed remainders are uniquely recognized.** The new group row gives
   `|r|<D/2`. The exact-power binomial expansion gives a canonical remainder
   `0<=rho<D/8`, and the retained numerator row gives `D|(r-rho)` regardless
   of the quotient's sign. Thus `|r-rho|<5D/8<D` and `r=rho`. All eleven
   old remainder and slack signs can be restored with fresh ternary
   witnesses. No sign is assumed in order to prove that same sign.

5. **Completeness has sufficient room for every group.** A four-pool group
   has at most five entries and the merged group has seven. Each canonical
   entry has absolute value below one eighth of its budget denominator.
   Hence the squared deficit is strictly positive even for seven entries:
   `4*sum rho_i^2<7D^2/16<D^2`. Integrality permits subtracting the explicit
   constant one and applying the ternary completion. Scaling the two t-level
   remainders by positive q transfers exactly the same bound to level t+1.

6. **The odd-square bootstrap is acyclic.** The added row gives q>=1.
   Orientation precedes the sign of q; the known positive t handles the
   base `F^2+1`, including its base-one possibility. The ceiling then gives
   F>=1 and B>=2. The genuine request `B^x` forces x>=0; the two endpoints
   strengthen this to x>=2 and the needed large lower bound. The base
   `q+1>=2` requests force the actual representative exponents nonnegative,
   giving H0>=1. Only now is `q=(BH0)^x>=B^2>B` used to recover the deleted
   output-slack sign. Each inference has its premises before use.

7. **The extra parity constraints are compatible in the converse.** With
   F=t!, all beta moduli are odd because y is even. Their odd product permits
   any sufficiently large even beta code x. Each `1+F^2/i` is odd, so B and
   N are odd. The representative CRT modulus N^2 is then odd, allowing
   independent parity choices. Opposite parities for a,b make the semantic
   anchor h even, and one of the seven remaining representatives sets the
   parity of their total so that H0 is odd. The same dominance intervals as
   the parent are retained. Thus `(BH0)^x` is an odd square with the required
   integral root. No restriction on every old zero is asserted or needed.

## Independent finite audit

`peer_literal_audit.py` imports no producer, projector, or parent program.
It reads the JSON solely as data. It verifies that:

- the source variable prefix is unchanged;
- exactly the eleven specified interval sign rows, and optionally the
  one stated front sign row, are deleted;
- all 398 or 397 other inherited residuals remain byte-equivalent as JSON
  data and in the same order;
- every newly appended budget, product, and odd-square residual has exactly
  the formula stated in the reviewed proof;
- every centered endpoint's complete expanded coefficient list is the
  exact independently calculated sum of squares of its literal residuals;
- every coordinate is live and the exact dimensions, degree, monomial
  count and coefficient height agree with the stated metrics.

The receipt `INDEPENDENT_LITERAL_REVIEW.json` binds the proof and all checked
sources/outputs by SHA-256. Its measured centered endpoints are:

| Variant | Integer variables | Quadratic rows | Degree | Collected monomials | Height |
|---|---:|---:|---:|---:|---:|
| Four pools | 261 | 185 | 4 | 5,332 | 128,446 |
| Three pools | 260 | 186 | 4 | 5,335 | 128,446 |
| Odd square, three pools | 258 | 186 | 4 | 5,319 | 128,446 |

These finite checks do not prove the unbounded consistency equivalence and
do not replace the mathematical proof. Together with that proof and its
explicit inherited calibration, they support the stated endpoints.

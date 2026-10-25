# Independent review: normalized binomial remainder certificates

Reviewer: a separate research agent, 25 October 2026.
Target: `agent_direct/NORMALIZED_REMAINDERS_PROOF.md` and the complete
`normalized_remainders` / `normalized_remainders_centered` artifact pair.
Pinned repository commit: `55d1f72aedebf892e446c90d35fa1ae37689b0f2`.

## Conclusion

The new mathematical reduction is sound and constructively complete relative
to the explicitly retained parent power/Pell, arithmetic, and C222-to-ZFC
refutation calibrations. The measured final equation has 252 unrestricted
integer variables, 182 quadratic residuals, exact degree 4, 5,340 collected
monomials, and coefficient height 128,446. Against the matched incoming
round-17 parent it saves 30 variables, 10 residuals and 151 collected terms
at unchanged degree and height. This review does not assert global minimality,
literature-wide priority, or a new end-to-end formal proof.

## Mathematical checks

1. The signed-frame and orientation-first parent establishes every power
   port before it invokes any of the eleven deleted interval guards.
   The three retained scalar guards suffice for the raw ceiling bootstrap.
   Therefore the new global cap is not used to justify its own positive
   denominator assumptions.
2. The strict-budget parent establishes `x>=2+(t+1)y`, `t>=16`, `y>=1`.
   Thus the four denominator types `q^t`, `q^(t+1)`, `q^(y+1)`, `q^x`
   divide `M=q^x`. Each new ratio is automatically a positive integer
   after interpreting the actual power ports.
3. In a normalized digit `v U=M Q+R`, divisibility `v|M` forces `v|R`.
   This remains valid when the quotient term is `N M Q`. Hence the
   restored remainder `R/v` is an integer; no unlicensed rational
   coordinate has been introduced.
4. The guard `M^2=1+4 sum R_i^2+G(a,b,c)` gives strict centered bounds.
   A least nonnegative residue below half the denominator is the unique
   congruent integer in the resulting symmetric interval. This restores
   the old nonnegative remainder and slack, rather than assuming their
   signs.
5. The factorial digit is handled before assuming `F=t!`. The elementary
   induction `binom(m+t,j)<=(m+1)^t` holds for `m>=1`, `0<=j<=t`.
   The raw ceiling gives `V0<B^2`, and `q>=B^x` with `x>=19` supplies
   the margin `V0/(q-1)<1/32`. Thus its low digit is small enough
   independently of the factorial fixed-point conclusion. The retained
   output slack still gives `B<q`, so the central coefficient is uniquely
   the true binomial coefficient.
6. Only after recovering `F=t!` does the proof use the encoded-index
   positivity and derived-label degree bounds. The ordinary coefficient
   estimate uses `max(1,a)` and therefore correctly covers zero global
   representatives. Every remaining low residue is below its denominator
   divided by 32.
7. Completeness uses the genuine canonical family, not arbitrary interval
   remainders. Its eleven normalized residues satisfy `R_i<M/32`, so
   `4 sum R_i^2<M^2`. Since the difference is an integer, the required
   slack `M^2-1-4 sum R_i^2` is nonnegative. The inherited ternary form
   `a^2+b^2+c(c+1)` represents every such slack.
8. The transformed digit numerators are products of existing output
   coordinates and new ratio coordinates, so they are quadratic.
   The three old `N L` product coordinates can be shared as the existing
   `N M` coordinate after normalization. The 30-variable count does not
   double count the old affine-eliminable interval slack coordinates.

## Independent finite audit

`audit_normalized.py` imports no producer module. It reconstructs the source
change directly from the exact parent source and its interval guard list.
It verifies all eleven bound deletions, all scaled numerator rows, the exact
factorial denominator change, the three range denominator aliases, the new
ratio rows, and all new guard rows. It then independently replays all 205
integral monic elimination steps, verifies the final integral translation,
and independently multiplies and collects every residual square. Every
coordinate is live in the final expanded polynomial.

Both normal and `python -O` invocations passed. The checks use explicit
exceptions, so optimized Python does not disable them. The companion
`audit_normalized_controls.py` rejects six separate one-field corruptions in
both modes: ratio coefficient, digit coefficient, budget coefficient,
restoration polynomial, translation shift, and final quartic coefficient.

The independent audit deliberately leaves the inherited Horn-factorization
map to the separately retained factorization checker. It does not claim to
have replayed that map or the whole logical formalization. The new source
transformation, guard layer, monic projection, translation, and final SOS
collection are independently checked here.

## Optional coefficient-two lemma

The primary artifacts retain the transparent coefficient four. As a proved
but unpromoted variation, the common guard coefficient may be replaced by
two under the same tiny-residue hypotheses: `2R^2<M^2` implies
`|R|<3M/4`, while a true residue below `L/32` differs from the restored
candidate by less than `25L/32<L`. Congruence therefore forces equality.
Completeness follows from `2 sum R_i^2<22M^2/1024<M^2`. This variation
has not been emitted or measured as a separate endpoint in this review.
Coefficient one does not support the generic uniqueness lemma: with
`M=L=100`, true remainder 1, the alternative remainder -99 remains
congruent and satisfies `R^2<M^2`. This is a counterexample to that generic
relaxation, not a claimed spurious zero of the completed ZFC polynomial.

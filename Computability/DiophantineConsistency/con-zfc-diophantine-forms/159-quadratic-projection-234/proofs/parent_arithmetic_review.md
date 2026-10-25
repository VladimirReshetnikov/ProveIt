# Independent audit of the shared-factorial-error arithmetic proof

## Scope and outcome

This is an independent ordinary-mathematics review conducted within the
AI-assisted research workflow. It is not an outside human referee report,
a new Lean/Rocq build, or an encoded derivation in object-language ZFC.

The source reviewed is the current incoming archive
`ConZFC_Shared_Factorial_Error_2026-10-25.zip`, obtained from ProveIt at
commit `7a8da414376a80b90ecf799f37ceb26fb9ac674e`. Its own comparison
snapshot is the earlier commit identified by that archive.

Byte identities:

* Incoming archive SHA-256:
  `8c126ebd9982e547f16e86cf65b57dbc85bf72e98032237ab0c324afc1694ef2`.
* `report/paper_main.tex` SHA-256:
  `d9cf03c92db7d68bffb1e51d81af58777ddec8b3cd4d1d681bfabdb9a55ad74e`.
* `equations/equation240/equation.json` SHA-256:
  `5d6b3b447dae75969bce826c30a61d216df784a396d5fed221983e1b23728cc0`.

**Outcome:** no gap was found in the shared-error/signed-radix arithmetic
replacement under its explicitly retained Pell-frame, exact-source,
binomial-range, and logical-calibration interfaces. In particular, the
sign recovery is acyclic. The new radical projections in the present
contribution require their own exact algebra verification; this note
does not claim to verify those projections.

The principal files read for this audit were the complete proof through
its constructive completeness section in `report/paper_main.tex`,
`verification/SIGNED_POWER_AND_BETA_REVIEW.md`, and the source mutation
in `equations/build_unified_bootstrap.py`. The former review file contains
historical alternative beta choices, but its Section 6 and the main
paper correctly identify the delivered choice as the original
`y=V(V-1)` with affine odd `q=2z+1`.

## 1. Pell orientation and signed centers

The proof requires the full fourteen-pair squared orientation pool.
Its squared frame is used before signs of `F,B,q,x` are established.
No shorter nine-pair orientation argument may be silently substituted:
over a provisionally negative base, a positive power output alone does
not determine the abscissa orientation.

The deterministic center argument is consistent with signed `A`.
Let the absolute anchor ordinate be `C=Y_i(|A|)` and let the absolute
common ordinate be `Y_l(|A|)`, with `C^2` dividing that common ordinate.
For `i>=2`, strong divisibility first gives `i|l`; writing `l=is`,
Pell composition and reduction modulo `C` give

\[
 Y_l(A)=Y_i(A)Y_s(X_i(A)),\qquad
 Y_s(X_i(A))\equiv sX_i(A)^{s-1}\pmod C.
\]

Since `gcd(X_i(A),C)=1`, the squared divisibility implies `C|s`.
Thus `C|l` and `l>i`. The comparison congruences supply
`j=+/-i mod 2l` and `j=+/-h mod C`, hence `i=+/-h mod C`.
The strict bound

\[
 C\ge i+2|A|-2>i+|h|
\]

forces `i=|h|`. Its use is not circular: `|h|<W` is already
available from the frame, while `2|A|-2>W` follows from the
independent large-center bound. The cap then bounds the other
indices by this anchor index.

If `i=1`, the cap forces `h=0` and all other ordinates zero.
The full orientation pool has an anchor-ordinate error equal to one;
all errors are small after these indices are classified. Thus its
nonnegative residue is nonzero and strictly smaller than `|A-1|`,
contradicting divisibility. This closes the exceptional unit-ordinate
case, including negative `A`.

After index bounds are obtained, each Pell pair has an abscissa
residue `+/-1` and ordinate residue equal to a signed index modulo
`A-1`. The error pool is below `4*14*(W^2+1)<4W^3<|A-1|`,
so every error vanishes. This indeed yields canonical pairs at
the requested signed indices.

The exact classification and separation lemmas are retained
interfaces, rather than newly formalized theorems in this review.
The application to the modified arithmetic front introduces no
new positivity premise.

## 2. The signed power lemma, including units

For `2<=|n|<W`, `|k|,|m|<W`, and `|A|>W^W`, the modulus

\[
 T=2An-n^2-1
\]

satisfies `|T|>W^W+W`. Modulo `T`, one has
`(n-A)^2=A^2-1` and `n(2A-n)=1`. Therefore the canonically
oriented Pell expression is `n^k` at a nonnegative index and
its multiplicative inverse at a negative index.

For `k>=0`, the difference from the framed output is below the
modulus. For `k=-j<0`, the congruence instead gives `mn^j=1 mod T`,
but `|mn^j-1|<|T|`; the forced equality is impossible over the
integers. This excludes negative exponents without assuming `n>0`.

At `n=epsilon=+/-1`, one must use the separate unit argument.
The sequence

\[
 f_k=X_k(A)+(\epsilon-A)Y_k(A)
\]

has `f_0=1`, `f_1=epsilon` and a reversible recurrence whose
coefficient `2A` is `2epsilon mod T`. It gives
`f_k=epsilon^k mod T` for all signed integers `k`. The output
bound upgrades this to equality. The use of this argument to
exclude `q=-1` is valid even before the sign of `x` is known.

## 3. The common error budget and early bounds

The altered rows are

\[
 Bv=M,\quad MF=vV+S,\quad
 M^2=1+4(S^2+\sum R_i^2)+G(a,b,c),
\]

where `G=a^2+b^2+c(c+1)>=0` over the integers. These imply
`M,B,v!=0`, `S=v(BF-V)`, and

\[
 |BF-V|<|B|/2.
\]

The known positive horizon first recovers
`V=(F^2+1)^t>=1`; at `F=0`, the base-one clause gives `V=1`.
Put `b=|B|` and `f=|F|`. If `F=0`, the error bound gives `b>=3`.
Otherwise opposite signs of `B,F` are impossible. If `b<=f`, then

\[
 V<b(f+1/2)\le f^2+f/2,
\]

contradicting `V>=(f^2+1)^2`. Thus `b>=f+1>=2`, and
`V<b(f+1/2)<b^2`. These are all obtained before either
factorial or binomial authenticity.

## 4. Radix and digit recovery

Oddness makes `q` nonzero. If it is a unit, the unit power lemma
gives `|M|=1`, contradicting `Bv=M` and `b>=2`. Hence
`Q=|q|>=3` and `|q+1|>=2`.

The requests at `q+1` now force the actual CRT representatives
nonnegative, yielding `H>=1`. The request at `q` gives `x>=0`
and `M=q^x`. The retained ratio `q^(t+1)*v_(t+1)=M` implies
`x>=t+1` by integer divisibility. The request at `BH` then gives
`q=(BH)^x` and `Q>=b^(t+1)`. This order does not assume `B>0`
or `q>0`.

For `F!=0`, every coefficient `binom(F^2+t,j)`, `0<=j<=t`,
is at most `V<b^2`. The uniform bound
`binom(m+t,j)<=(m+1)^t` for `m>=1` follows by Pascal induction;
the new right edge is bounded by the product formula. For `F=0`,
the main proof correctly uses the separate bound `2^t`, since
`V=1` cannot bound those coefficients.

Thus the signed low polynomial at either sign of `q` has absolute
value below `Q^t/32`. The normalized row gives an integral
remainder of absolute value below `Q^t/2`. Both are congruent
modulo `q^t`, so their difference is a multiple of `q^t` of
smaller absolute value and is zero. The digit congruence is
therefore `B=binom(F^2+t,t) mod q`.

The difference from this positive binomial is less than `Q`:
for `F!=0`, use `b+b^2<b^(t+1)`; for `F=0`, the binomial
is one and `b+1<b^(t+1)`. Hence equality is exact. It excludes
`F=0`, and the already established agreement of signs makes
`F>0`. Finally `q=(BH)^x>0`. No circular sign step was found.

## 5. Nearest-factorial uniqueness

The strengthened lemma required by the symmetric error is valid.
For `t>=16` and `F>=1`, put

\[
 R_t(F)=\frac{(F^2+1)^t}{\binom{F^2+t}{t}}
 =t!\prod_{i=2}^t\left(1-\frac{i-1}{F^2+i}\right).
\]

If `|F-R_t(F)|<1/2`, monotonicity in `F` gives
`R_t(F)>=2^t/(t+1)>t^2+1/2`, hence `F>t^2`. The elementary
product lower bound yields

\[
 R_t(F)>t!\left(1-\frac{t(t-1)}{2F^2}\right)>\frac34t!,
\]

so `F>t!/2`. Applying the same estimate again gives
`0<t!-R_t(F)<2t(t-1)/t!<1/32`. Therefore
`|F-t!|<17/32<1`, and integrality forces `F=t!`.
At `F=t!`, the direct estimate
`0<F-R_t(F)<t(t-1)/(2t!)<1/32` proves the converse.

These bounds hold with a very large margin at `t=16` and
propagate by elementary induction. In particular the second
application uses the newly obtained `F>t!/2`, not an assumed
factorial equality.

The old nonnegative scalar slacks are now legitimately restored:
`s=BF-V` is a positive integer below `B/32`,
`r=B-s-1>=0`, and `q-B-1>=0`. The restored beta definition is
literally the original `y=V(V-1)`, so the source returns to the
retained arithmetic interface.

## 6. Remaining bounds and completeness

The endpoint implications `x>=F+1` and `x>=2+(t+1)y` are
valid after the recovered `F=t!` and `y>F+2`. They imply
`2+t+x+y+F<2x` and `x>2^32`. The numeric comparison
`2^23 log_2(2x)<x` is true at `2^32` and thereafter, so the
retained local-polynomial bound is below `2^x` as required.

The index row excludes the zero actual index representative,
making `H>=2`. The ordinary and derived-label coefficient
bounds then give each remaining low remainder below its
denominator divided by 32. The normalized common norm selects
these remainders uniquely. The inherited binomial range and
prime-power extraction interfaces can therefore be applied
with their original strict hypotheses.

In the reverse construction, all original reciprocal factors
`1+F^2/i` are odd. Consequently the CRT precision modulus is
odd and representatives can be parity adjusted without
changing any residue. Choosing the dominant `a` with parity
opposite to `b` makes the semantic anchor even; a third
independent representative sets `H` odd. The same magnitude
windows have representatives of both parities.

At an even anchor `h`, the canonical `C=Y_h(A)` is even and
`U=X_h(A)` is odd. Choosing `l=hC` gives
`J=CY_C(U)`. The binomial expansion, with
`U^2-1=(A^2-1)C^2`, shows

\[
 Y_C(U)/C\equiv U^{C-1}\pmod C.
\]

Each nonleading term is divisible by `C` after the division,
so `J/C^2` is indeed an odd integer. The deterministic-center
witness therefore exists under exactly the retained parity condition.

Finally `v=M/B` is integral and `S/M=F-V/B<1/32`. All eleven
other normalized errors have the same strict margin. Therefore

\[
 4(S^2+\sum R_i^2)<48M^2/1024<M^2.
\]

The remaining integer norm gap is nonnegative and has the
required ternary `G` representation. Completeness introduces
no additional large-value or sign obstruction.

## 7. Boundaries of this conclusion

This review checks the mathematical compatibility and new
arithmetic claims just described. It does not independently
rebuild the entire historical C222 syntax development, every
transitive Pell source, or a proof assistant environment. The
named inherited interfaces remain explicit dependencies:
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`, together
with the recorded arithmetic source-to-equation certificates.

Finite coefficient checks certify a specific literal polynomial
and its exact projections. They do not replace any of these
unbounded mathematical arguments. No statement here proves
`Con(ZFC)` or decides whether the polynomial has an integer zero.

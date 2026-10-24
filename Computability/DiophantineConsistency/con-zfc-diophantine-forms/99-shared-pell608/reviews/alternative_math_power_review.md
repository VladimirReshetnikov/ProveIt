# Independent review of oriented Pell power witnesses

## Verdict

The proposed restrictions preserve the graph `m = n^k` in the positive-base,
positive-exponent branch. They are sound restrictions of the original
Pell--Matiyasevich certificate, and the standard completeness construction
has witnesses satisfying every restriction. I found no circularity. The
argument applies independently at each call; inactive Boolean-guarded
branches remain harmless.

The source reviewed is `research/mathlib/PellMatiyasevic.lean`, the proofs of
`matiyasevic` and `eq_pow_of_pell`, together with the incoming builder's
literal `Builder.power` macro. This is an ordinary mathematical review,
not a new Lean check.

## Notation

For an integer parameter `a >= 2`, define natural Pell sequences by

    X_a(0) = 1,   Y_a(0) = 0,
    X_a(j+1) = a X_a(j) + (a^2-1) Y_a(j),
    Y_a(j+1) = X_a(j) + a Y_a(j).

They satisfy `X_a(j)^2 - (a^2-1)Y_a(j)^2 = 1`.
The positive branch assumes `n >= 1` and `k >= 1`.

## 1. Deterministic majorant W = n+k

The original criterion needs only `n <= W`, `k <= W`, and

    A^2 - ((W+1)^2-1)(W Z)^2 = 1,   A >= 2.

Set `W = n+k`; then both inequalities hold automatically. For completeness,
take `A = X_{W+1}(W)`. The standard congruence
`Y_{W+1}(W) = W (mod W)` gives `W | Y_{W+1}(W)`, so the natural quotient
`Z = Y_{W+1}(W)/W` exists. Also `W > 0` and `A > 1`.

The original bound proving `m < T`, where
`T = 2 A n - n^2 - 1`, still holds verbatim:

    n^k <= n^W < (W+1)^W <= X_{W+1}(W) = A.

The subsequent `eq_pow_of_pell_lem` proof depends only on this strict
inequality and on `n,k > 0`. It gives `n^k < T`.
No property peculiar to `max(n,k)` is used.

Thus the three free witnesses `W`, `wn`, and `wk` can be deleted,
substituting the affine expression `n+k` wherever `W` occurs. If the
builder temporarily creates an addition gate, its affine elimination is
a separate implementation detail; the mathematical dimension saving is
three.

## 2. Orienting B congruent A modulo U

For the standard certificate of `X = X_A(k)`, `Y = Y_A(k)`, use

    M = 2 k Y,
    U = X_A(M),   V = Y_A(M).

Since `k,Y >= 1`, `M >= 2`, and strict increase in the index gives `U > A`.
The existing proof establishes `gcd(U,4Y)=1`, then chooses a natural
Chinese-remainder witness

    B = A (mod U),   B = 1 (mod 4Y).

Because `0 <= A < U`, every nonnegative `B` in this residue class has
`B >= A`. Consequently the congruence admits the oriented representation

    B = A + U q_B,   q_B in N.

Conversely this equality implies the original congruence without any
additional assumption.

## 3. Orienting S congruent X modulo U

The standard construction sets `S = X_B(k)`, `R = Y_B(k)`.
From `B >= A >= 2`, joint induction in the displayed Pell recurrences
gives

    X_B(j) >= X_A(j),   Y_B(j) >= Y_A(j)  for every j in N.

Indeed all recurrence coefficients and both initial coordinates are
nonnegative, and each coefficient for `B` dominates the corresponding
coefficient for `A`. In particular `S >= X`. The source proof already
gives `S = X (mod U)`, so

    S = X + U q_S,   q_S in N.

This does not infer monotonicity from the certificate equations; it is
used only to select canonical completeness witnesses. For soundness the
oriented equality implies the old congruence directly.

## 4. Orienting R congruent k modulo 4Y

The elementary sequence bound `Y_B(k) >= k` gives `R >= k`. Together
with the existing congruence `R = k (mod 4Y)`, this yields

    R = k + 4Y q_R,   q_R in N.

Again the reverse implication to the original congruence is immediate.

## 5. Orienting the power congruence

The proposed equality is

    X + Yn = YA + m + T q_P,   q_P in N.

For the canonical witnesses, `m=n^k`, `X=X_A(k)`, and `Y=Y_A(k)`.
The Pell recurrence gives, for `k >= 1`,

    X_A(k) - A Y_A(k) = -Y_A(k-1).

Hence its left-minus-first-right term is

    L := X + Yn - YA = n Y_A(k) - Y_A(k-1) > 0,

because `n >= 1` and `Y_A(k) > Y_A(k-1)`. The original power argument
proves `L = m (mod T)`, and its bound gives `0 < m < T`.
Write `L=m+Tq` with an integer quotient. If `q <= -1`, then
`L <= m-T < 0`, contradicting `L > 0`. Therefore `q >= 0`, furnishing
the proposed natural witness.

This positivity argument avoids any need to guess the sign of a general
congruence quotient. It uses only the canonical completeness witnesses.

## 6. Removing the B >= 2 slack

Replace

    B = 1 + 4Y q4

by

    B = 1 + 4Y (q4_new+1),   q4_new in N.

For soundness, `Y >= k >= 1` follows from the retained index bound before
using the third Pell norm. Thus this equality gives `B >= 5`, and the
separate `B >= 2` slack is redundant.

For completeness, the canonical `B >= A >= 2` is congruent to `1` modulo
`4Y`. Its natural quotient `(B-1)/(4Y)` cannot be zero, since that would
give `B=1`. Subtracting one therefore yields `q4_new in N`.

## 7. Removing the A >= 2 slack

The retained equations imply `A >= 2` independently of any Pell theorem.
Indeed,

    2An = T + n^2 + 1,   T = m + gap + 1 >= 1.

If `A <= 1`, then `2An <= 2n <= n^2+1`, the last inequality being
`(n-1)^2 >= 0`. This contradicts `2An = T+n^2+1 > n^2+1`.
Thus the `a2` witness and its defining row can also be removed. This
does not need `m>0`; natural `m` and the positive gap are enough.

## 8. Quantified witness maps and count

For soundness, reconstruct the old certificate using `W=n+k`,
`wn=k`, `wk=n`, `a2=A-2`, `b2=B-2`, and `q4_old=q4_new+1`.
For an old `congruent(left,right,modulus)` row implemented as
`left + modulus*qp = right + modulus*qm`, the new oriented row
`left = right + modulus*q` lifts by `qp=0`, `qm=q`.
This applies to all four congruences with the orientations stated above.

For completeness, take the canonical witnesses in Sections 1--6 and the
four nonnegative difference quotients. The original `yk`,
positive-`V` quotient, and output-gap witnesses remain natural by the
same inequalities already proved in the original construction.

At the level of freely quantified natural witnesses, the changes remove
3 (`W,wn,wk`) + 4 (one quotient from each pair) + 1 (`b2`) + 1 (`a2`) = **9**
witnesses per positive power macro. Remaining gate-count and total-quartic
improvements depend on the literal builder's affine elimination and
sharing; they must be measured independently.

In a general power macro, when the positive-case Boolean selector is zero,
the new mathematical rows are disabled. Unguarded arithmetic gate rows
still have their uniquely determined natural evaluations, so any chosen
natural values of the remaining free witnesses extend to those gates.
There is no new obstruction to the zero-base or zero-exponent branch.

## 9. One-product form of an unguarded Pell norm

For natural `a,x,y`, introduce only `H=ay` and impose the quadratic row

    x^2 + y^2 - H^2 - 1 = 0.

Together with the quadratic row `H-ay=0`, this is exactly equivalent to
`x^2-(a^2-1)y^2=1`. The witness is uniquely `H=ay`, and is natural.
In particular the first norm can reuse the existing `AY` register from
the power-congruence row. Squares occurring directly as terms of a
quadratic residual need not be separately allocated register variables.

For `y=WZ`, first allocate the product `WZ`; then allocate `(W+1)(WZ)`.
The final norm is `A^2+(WZ)^2-((W+1)WZ)^2-1=0`. This is still a system
of quadratic rows with natural intermediate products.

This optimization is valid as stated for unguarded rows. Multiplying its
quadratic residual by a Boolean case selector would generally produce a
cubic row; a guarded implementation must retain an appropriate separate
gate expansion or another sound quadratic construction.

## 10. Affine aliases

The substitutions `Y=k+yk` and `T=m+gap+1` with `yk,gap in N` are exact
parametrizations of the retained bounds. They replace old witnesses
`Y,T` and their defining equations by affine expressions and have explicit
inverse maps `yk=Y-k` and `gap=T-m-1` on the old solutions. All occurrences,
including products and norms, must use the same aliases. No gate whose
defining expression can take negative values is being eliminated merely
on an unsupported positivity assumption.

The earlier count of nine removed *free* witnesses assumes explicit
`Y,T` slots; after any affine aliases and eliminations, count the actual
remaining variables rather than adding that headline number a second
time. The standalone fixture checker supplied beside this note verifies
canonical positive certificates for `(n,k)=(1,1),(2,1),(1,2)`.

# Elementary stability operations for the balanced-core proof

Independently approved October 1, 2026. These are proof simplifications for the unified article or a future revision; the delivered role-cover archive is unchanged. No novelty claim for these elementary operator identities.

## Physical merge

For f(a,b,w)=ab A(w)+a B(w)+b C(w)+D(w),

    [d/dt f(t,t,w)]_(t=z/2) = z A+B+C.

Thus the physical merge ab↦z, a↦1, b↦1, 1↦0 preserves stability or gives zero by diagonalization, differentiation and positive scaling. In the monomer application the empty-support coefficient rules out zero. See MERGE_BY_DIFFERENTIATION.md.

## Asano-type coefficient contraction

For the same multiaffine f define C_ab(f)=D−A. If f is stable, then

    g(t,w)=t f(t,−1/t,w)=B t²+(D−A)t−C

is a stable polynomial: both t and −1/t lie in the upper half-plane whenever t does, and multiplication by t introduces no upper-half-plane zero. Differentiation and real boundary specialization give

    g'(0,w)=D−A.

Both operations preserve stability or produce the zero polynomial. Hence C_ab has the same preservation property. The statement permits arbitrary untouched variables w and does not require nonnegative coefficients.

## Single-edge gluing

Starting with a polynomial multiaffine in a,b, substitute fresh upper-half-plane variables x,y through f(a+x,b+y,w). This is stable. Apply C_xy to obtain

    C_xy[f(a+x,b+y,w)] = f(a,b,w)−∂a∂b f(a,b,w).

This proves the single-edge gluing operator1−∂a∂b preserves stability or zero without invoking the general finite-degree symbol classification.

## Complete rank-two coupling

For rank-two parallel-class sums r_i let B=e2(r), L=sum(r). Polarize the auxiliary quadratic into

    F(s1,s2)=s1s2+(L/√2)(s1+s2)+B.

If f(s)=s²+√2 Ls+B is the approved rank-two quadratic, then

    F(s1,s2)=f((s1+s2)/2)−(s1−s2)²/4.

The invertible real linear change to the average and difference variables shows that the quadratic form of F has exactly one positive direction. Its coefficients are nonnegative, so F is strictly positive on the positive orthant. The elementary orthogonality argument from the original quadratic proof therefore proves F stable directly; no polarization theorem is needed.

Take the product F_P(s1,s2)F_Q(t1,t2) on disjoint variable sets and apply C_(s1,t1), followed by C_(s2,t2). Put α=L_P/√2 and β=L_Q/√2. After the first contraction the polynomial is

    B_P B_Q−αβ + s2(α B_Q−β)+t2(β B_P−α)
      +s2t2(αβ−1).

The second contraction gives

    B_P B_Q−2αβ+1 = B_P B_Q−L_P L_Q+1.

Each contraction preserves stability or zero, and the final constant coefficient1 excludes zero. This is exactly the coupling required in the complete balanced-core proof.

## Dependency boundary

Together these identities remove the need for the full Borcea–Brändén operator-classification theorem from the physical merge, single-edge gluing and complete-core coupling steps. The all-real multiaffine Rayleigh criterion used for the incomplete-core square identities remains a separate mathematical dependency. The delivered archive's use of the symbol theorem is correct and does not require replacement.

The standard closure operations used here are recorded in Wagner's survey, Lemma2.4(b)–(f), including real specialization by Hurwitz continuity: https://www.math.uwaterloo.ca/~dgwagner/ceb_wagner.pdf .

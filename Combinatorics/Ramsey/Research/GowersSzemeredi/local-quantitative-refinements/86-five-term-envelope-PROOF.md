# An explicit five-term comparison with the paper's numerical threshold

## Result and scope

Fix ProveIt commit `af74fb522c24a6331886b11db76942642a6a0e42`. Let

- H_f(δ) = `fejerFiveTermThreshold δ`;
- T(δ) = `szemerediThreshold δ 5`.

For every real 0 < δ ≤ 1/2, the finite expressions at this revision satisfy

    H_f(δ) < 2^(2^(δ^(-2^76))) < T(δ) = 2^(2^(δ^(-2^16384))).

The exponent 2^76 is deliberately generous and is not asserted optimal. The proof below in fact yields the stronger intermediate bound

    log₂ log₂ H_f(δ) ≤ x^(2^67),
    x = 2/α,  α = (δ^5/64000)^16.

This is a real-variable proof about the actual source expressions. The paper threshold is checked against the pinned transcription, the original paper's explicit right-association convention, and the pinned Lean definition. It is not a claim of independent Lean compilation, complete verification of the progression theorem's import closure, or a literature-best result.

The source contains `natural_five_term_fejer`, which supplies the progression implication for H_f on 0 < δ ≤ 1. In contrast, `theorem_18_2` in Sections17_18.lean is a Prop-valued definition of the paper's target statement. This comparison does not mistake that target definition for a proved Lean theorem.

## 1. Conventions and elementary estimates

Throughout, log means log₂ unless explicitly written ln. All real-power bases in this proof are positive. Maxima can be reassociated freely. For y ≥ 2, a nonnegative integer m and t ≥ 0,

    2^m ≤ y^m,  log₂ y ≤ y,  ceil(t) ≤ t+1.

For t ≥ 1, ceil(t) ≤ 2t. For B ≥ 4,

    B² ≤ 2^B,  5B²+6B ≤ 2^(2B),  log₂ B ≤ B.

The second estimate follows from 5+6/B ≤ 8, the first estimate, and B+3 ≤ 2B. Also 1/2 ≤ ln 2 < 1 and 1 < π < 4.

Write

    PP(C,D,e) = max{1, max{1,C/D}^(1/e)}.

This is `positivePowerThreshold C D e`. For C,D,e > 0,

    log PP(C,D,e) = max{0,log(C/D)}/e.

The source uses Lean's totalized division: 1/0 = 0. Thus PP(C,D,0)=1 whenever it occurs below. This matters for the q=0 term of each finite spectral maximum; that term must not be discarded without explanation.

## 2. Exact common Fourier dependencies

The common threshold is

    F(α) = max{ F_graph(α), G((α/2)^D) },  D=4207554485.

Here F_graph is `section13FrequencyGraphThreshold`, and G is `section13GeometricThreshold`. We now bound every branch of G, including both finite maxima and both square thresholds.

### 2.1 Primitive geometric parameters

Temporarily fix 0 < γ ≤ 1, and set

    y=2/γ,  B=y^(2^32),  L=log₂(1/γ).

In particular y≥2 and B≥2^(2^32)>323. The relevant exact parameters reduce to

    θ = 2^-59 γ^176,
    θ₁ = 2^-620025 γ^1843952,
    Q_bound = 2^620143 γ^-1844304,
    Q = 2^(2^20) γ^(-2^21),
    K = 2^114 γ^-320,
    c = 2^(-228K-1) γ^(576K),
    d₀ = θ₁/(64π),  d=min{1,d₀/2},
    k = ceil(K),
    z = 2^(-155k) (γ^32/16)^(18k)/k,
    e = 2^(-13Q),
    f = 2^-100 γ^448,
    g = 2^-284 γ^1408,
    W = 2^135 γ^-704.

These are respectively the Section 10 cutoff and Section 13 initial coefficient and spectrum bound; the Section 13 large parameter and radius; the integer-rounded Section 10 radius; and the square parameters. In particular k, the ceiling in the radius z, is retained.

For 1≤q≤floor(Q_bound), put

    u_q = θ₁²/(16q).

The following bounds all hold:

    q,Q,d₀^-1,d^-1,u_q^-1,f^-1,g^-1,W ≤ B,
    log(c^-1),log(z^-1) ≤ B,
    0<c,d₀,d,z,f,g≤1,
    e^-1 ≤ 2^(13B).

Here are explicit checks sufficient for the bounds, avoiding any numerical evaluation of a tower:

- Q ≤ y^(2^20+2^21) ≤ y^(2^22)
- Q_bound ≤ y^2464447 ≤ y^(2^22)
- d₀^-1 ≤ y^2463985 ≤ y^(2^22); d=d₀/2, so d^-1≤y^(2^22+1)
- u_q^-1 ≤ y^(4+2^22+2·2463977) ≤ y^(2^24)
- f^-1≤y^548, g^-1≤y^1692, W≤y^839
- K≤y^434 and k=ceil K≤2K≤y^435
- Since 228+576L≤228+576y≤690y≤y^11,
  log(c^-1)=1+K(228+576L)≤y^446
- Likewise 227+576L≤y^11, and
  log(z^-1)=k(227+576L)+log k≤y^447

All the displayed exponents are at most 2^32. Each of c,d₀,d,z,f,g is positive and at most one directly from its exact formula (K,k≥1); d₀<1 also justifies d=d₀/2.

### 2.2 The recurrence branch, including finite suprema and ceilings

At polynomial degree two the exact source constants are

    P₂=2048=2^11,
    W₂=polynomialPartitionThreshold(2)=2^(2^321),
    simultaneousPolynomialThreshold(2,q)=(2W₂)^(2048^(q-1)).

Here q-1 is natural subtraction. For q≥1 it is ordinary subtraction. Write

    v_q=2^(-12q),
    R_q=max{ simultaneousPolynomialThreshold(2,q)+1,
             PP(8,1,v_q), PP(160+2γ^32,γ^32,v_q) }.

This is exactly `section13RecurrenceLengthThreshold γ q`. Uniformly for 1≤q≤floor(Q_bound),

    log R_q ≤ 2^(13B).

Indeed, the log of the first entry is at most

    1+(1+2^321)·2^(11(q-1)) ≤ 2^(323+11B) ≤ 2^(12B).

The second is 3·2^(12q)≤2^(13B). The third is at most

    (8+32L)·2^(12q) ≤ B·2^(12B) ≤ 2^(13B).

The last inequality uses 8+32L≤B, immediate from L≤y and B=y^(2^32).

The initial threshold is

    I_q=PP(R_q+2,d₀,u_q).

As R_q≥1,

    log I_q ≤ B(2^(13B)+2+B) ≤ 2^(15B).

I_q≥1, so

    log ceil(I_q) ≤ 1+2^(15B) ≤ 2^(16B).

For q=0, u_0=0 by totalized division, whence I_0=1 exactly; no estimate of u_0^-1 is needed. The full recurrence threshold is the maximum of 3 and the finite supremum of ceil(I_q) for 0≤q≤floor(Q_bound). Therefore

    log(section13DensityRecurrenceThreshold γ) ≤ 2^(16B).

The number of terms in a finite maximum introduces no multiplicative loss.

### 2.3 The integer-budget branch

The exact rounded-power threshold is

    V= max{ PP(1,c,e), PP(4,d,e), PP(1,zd,e) }.

Thus

    log V ≤ (2B+2)·2^(13B) ≤ 2^(15B).

The other term of `section13IntegerBudgetThreshold γ q` is PP(4,d₀,u_q). For q≥1 its logarithm is at most (2+B)B≤2^(15B); for q=0 it is exactly 1 before taking the logarithm. Hence the whole integer-budget threshold is at most 2^(2^(15B)). Its natural ceiling has logarithm at most 2^(16B).

The definition takes the finite supremum of those ceilings over 0≤q≤floor(Q_bound). Consequently

    log(section13DensityIntegerThreshold γ) ≤ 2^(16B).

This accounts for the Bohr-radius ceiling k, each threshold ceiling, the natural floor in the spectral upper limit, and q=0.

### 2.4 Both square branches

The exact square-length threshold is

    J=max{PP(8,1,f), PP(W,1,f), PP(8,(1/4)^g,fg)}.

Its logarithm is at most 5B², since the three logarithms are bounded respectively by 3B, B², and (3+2g)/(fg)≤5B².

The square-scale threshold is PP(J,c,e), so

    log(squareScaleThreshold) ≤ (5B²+B)·2^(13B) ≤ 2^(15B).

The square-power threshold is

    max{PP(4,c^f,ef), PP(2,(c^f/4)^(g/2),efg/4)}.

The first logarithm equals (2/f+log(c^-1))/e. The second equals

    (4/(fg)+2log(c^-1)+4/f)/e.

They are at most (4B²+6B)·2^(13B)≤2^(15B). Therefore both square branches are covered. Combining them with the preceding two finite maxima and the outer max with 1 gives the proved geometric estimate

    log₂ G(γ) ≤ 2^(16(2/γ)^(2^32)).                   (G)

### 2.5 Substitution and frequency purification

Return to x=2/α≥2 and γ=x^-D, where D=4207554485<2^32. Then

    y=2x^D≤x^(D+1)≤x^(2^32),
    B≤x^(2^64),
    16B≤x^(2^64+4)≤x^(2^65).

Estimate (G) gives

    log₂ G(x^-D) ≤ 2^(x^(2^65)).

The frequency branch is polynomial in x, despite its two natural ceilings. Put

    h=14409429,
    j=97h+336=1397714949.

Its exact purification parameters are δ₀=x^-h, ρ=x^-j, η=2^-44. Thus

    M=ceil(2^78 x^j)≤2^79 x^j≤x^(j+79),
    F_graph=max{2M, ceil(2^175 M^63 x^(j+15h))}.

All arguments being at least one, the final ceiling is bounded by twice its argument. Therefore

    F_graph≤x^(64j+15h+5153)=x^89669903324≤x^(2^37).

The first branch 2M is also bounded by that power. In particular its logarithm is at most x^38, and so the complete common threshold satisfies

    log₂ F(α) ≤ 2^(x^(2^65)),  0<α≤1.               (F)

No monotonicity assumption about the finite maxima in F has been used.

## 3. Exact Fejér local and final expressions

The following are the reductions of the actual Fejér definitions, as in the pinned Report296 source audit. They are reproduced to make the present bound independently readable.

    d=2^42,  P=2359296,
    a=2^-69 x^-(d+2),  μ=2^-57 x^-(d+2),
    b(a)=2^-20 a²(a/2)^12359,
    t=2^-30(a/2)^24718,
    w=μb(a),  β=w/2,
    e_f=2^(-x^(2^53)),  σ=e_f t/(2P).

To distinguish this localization e_f from the geometric e in Section 2, we retain its subscript.

For j=1,2,3 define

    P_j=(j!)²2^((j+1)²),
    W_j=2^(2^(40j³+1)),
    L_j(η)=max{W_j,(4π/η)^P_j,4^P_j}+4,
    Bdry(ε)=L_1(4πε),  B₀=Bdry(1/16).

The square in the source's polynomialPartitionThreshold is included in W_j. In particular log W_1=2^41, log W_2=2^321, log W_3=2^1081.

The phase constants and quadratic threshold are

    K_count=max{1,2B₀8^(1-t)},  D_count=K_count12^t,
    C=L_3(w)D_count^(1/P),
    E(a)=exp((4+6L_2(1))(2/a)^25378984).

With PP(z,1,u) written PP₁(z,u), the remaining exact maxima are

    O=max{F(α),PP₁(4,e_f)},
    U=max{256,O,PP₁(12max{2,max{4,E(a)}},e_f)},
    T_local=max{U,PP₁(C,σ)},
    S=max{5,T_local,32/β,12801/δ^5},
    c_iter=β/(8Bdry(β/64)),
    n=ceil(8/β),
    A=1+ln(max{1,S})+|ln c_iter|,
    Q_iter=2max{1,16/σ},
    H_f=exp(A Q_iter^n).

All constants, maxima and final iteration ceilings are retained here. The following bounds only increase them.

## 4. Propagation through the complete Fejér threshold

### 4.1 Discrepancy, size exponent, and iteration ceiling

The exact monomial simplifications are

    β=2^-865346 x^(-12362(d+2)),
    t=2^-1730290 x^(-24718(d+2)).

Consequently β<1, t<1, σ<1, and

    β^-1≤x^(2^56),    t^-1≤x^(2^57).

The sufficient integer inequalities are

    865346+12362(d+2) = 54368650971157718 < 2^56,
    1730290+24718(d+2) = 108710913663248398 < 2^57.

Since 2P<2^23,

    log(σ^-1)≤23+x^(2^53)+2^57 log x≤x^(2^54).

For the last step, 23+2^57 log x≤x^59≤x^(2^53), then absorb a factor 2. Thus

    log Q_iter = 5+log(σ^-1) ≤ x^(2^55).

The natural ceiling obeys

    n≤8/β+1≤9/β≤x^(2^57).

It follows that

    n log Q_iter ≤ x^(2^57+2^55)≤x^(2^58).          (I)

### 4.2 Boundary refinement and phase count

Using 0<β≤1, the exact boundary expression gives

    log Bdry(β/64)
      ≤1+max{2^41,16(6+log β^-1),32}
      ≤x^63.

For example 96+2^60 log x≤x^62, and the other maximum entries are no larger; the extra 1 is absorbed by x^63. Hence c_iter<1 and

    log(c_iter^-1)≤3+2^56 log x+x^63≤x^65.          (B)

At ε=1/16, B₀=W_1+4≤2W_1. Since 0<t<1, K_count=2B₀8^(1-t), and D_count≤192B₀. Therefore log D_count≤2^42≤x^42.

Since w=2β≤1 and w^-1≤β^-1,

    log L_3(w)
      ≤1+max{2^1081,P(4+log β^-1),2P}
      ≤x^1082.

Here P<2^22, so P(4+log β^-1)≤x^81. Consequently

    log C≤x^1083,
    log PP₁(C,σ)≤x^1083·2^(x^(2^54))≤2^(x^(2^55)). (C)

### 4.3 The quadratic threshold and its localization

The huge constant in E(a) is retained. Since π<4,

    L_2(1)=W_2+4≤2W_2.

Indeed the other entries in that maximum are at most 2^8192 and 2^4096, below W_2=2^(2^321). Thus

    (4+6L_2(1))/ln 2 ≤ 2^(2^323).

Also 2/a=2^70 x^(d+2)≤x^(d+72), and

    25378984(d+72)<2^68.

It follows that

    log log E(a)≤2^323+2^68 log x≤x^324,
    log E(a)≤2^(x^324).

E(a)>4, so the inner maximum in U is exactly E(a); it is not silently dropped. Hence

    log PP₁(12E(a),e_f)
      ≤2^(x^(2^53))·(4+2^(x^324))
      ≤2^(x^(2^54)).                              (E)

The PP₁(4,e_f) term is bounded the same way. Combining (F), (C), (E), and 256 yields

    log T_local≤2^(x^(2^65)).

For the additional entries of S, log(32/β)≤5+2^56 log x. Moreover δ^-5≤x from the exact relation x=2·64000^16 δ^-80 and δ≤1. Therefore log(12801/δ^5)≤14+log x. Both are bounded by 2^(x^(2^65)), as is log 5. We conclude

    log S≤2^(x^(2^65)).                            (S)

### 4.4 Final density iteration

S≥5, c_iter<1, and ln 2<1. Using (B) and (S),

    A≤1+2^(x^(2^65))+x^65≤2^(x^(2^65)+1),
    log A≤x^(2^66).

Because H_f=exp(A Q_iter^n) and 1/2≤ln2,

    log log H_f
      = log A+n log Q_iter-log(ln2)
      ≤x^(2^66)+x^(2^58)+1
      ≤x^(2^67).

Thus H_f≤2^(2^(x^(2^67))). This proves the claimed intermediate estimate with every branch of the starting threshold and every iteration factor covered.

## 5. Conversion to density and strict comparison with the paper

For 0<δ≤1/2, 64000<2^16 gives

    x=2·64000^16 δ^-80 < 2^257 δ^-80 ≤ δ^-337.

Since 337<2^9,

    x^(2^67) < δ^(-337·2^67) < δ^(-2^76).

Therefore

    H_f(δ) < 2^(2^(δ^(-2^76))).

The exponent comparison is strict because 0<δ<1 and 2^76<2^16384:

    2^(2^(δ^(-2^76))) < 2^(2^(δ^(-2^16384))) = T(δ).

The paper's Theorem 18.2 explicitly defines its arrow notation as right-associated ordinary exponentiation, then writes 2↑2↑δ^-1↑2↑2↑(k+9). At k=5 this is precisely the final expression above, not a six-level tower with an unspecified association.

## 6. What this closes and what it does not

This closes the mathematical comparison of the exact pinned Fejér five-term starting threshold against the pinned numerical Theorem 18.2 threshold throughout the paper's stated density range. The common F(α) is no longer an unbounded black box: its entire defining numerical dependency tree is bounded above in Section 2.

The present result does not claim that the old explicit interface exceeds the paper bound, that the exponent 2^76 is optimal, that the least sufficient integer thresholds are separated, or that all arbitrary-length induction dependencies have been audited. The weaker local-versus-old comparison in Report296 and the present paper comparison are different statements. No Lean files were modified or compiled, and no code from the upstream repository was executed.

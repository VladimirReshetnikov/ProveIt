# Independent mathematical review of the new syntheses

Review date: 23 October 2026. Source comparison pin: ProveIt `ae3007ca4467011e0e051c84acb4a1dd13971b0e`.

## Verdict and scope

The following new reductions withstand the mathematical challenges examined here:

| Construction | Domain | Equations | Exact degree | Binary operations |
|---|---:|---:|---:|---:|
| Two-weight norm, product | 12 positive integers | 1 | 1081 | 120 |
| Two-weight norm, comparison system | 12 positive integers | 3 | 1072 | 115 |
| Signed-scale original norm, product | 24 integers | 1 | 2432 | 163 |
| Signed-scale original norm, comparison system | 24 integers | 3 | 2416 | 158 |
| Signed-scale split-weight norm, product | 24 integers | 1 | 2256 | 164 |
| Signed-scale split-weight norm, comparison system | 24 integers | 3 | 2240 | 159 |
| Signed-scale ratio-weight norm, product | 24 integers | 1 | 1936 | 168 |
| Signed-scale ratio-weight norm, comparison system | 24 integers | 3 | 1920 | 163 |
| Re-evaluation of package 18's polynomial | 9 natural integers | 1 | 161844·5^33+484 | 1616 |
| New natural-domain majorants | 9 natural integers | 1 | 120764·5^33+368 | 1673 |
| New majorants with positive shifts | 9 positive integers | 1 | 120764·5^33+368 | 1668 |
| Exact coefficient folding, package-18 polynomial | 9 natural integers | 1 | 161844·5^33+484 | 1485 |
| Exact coefficient folding, new majorants | 9 natural integers | 1 | 120764·5^33+368 | 1542 |
| Exact coefficient folding, new majorants | 9 positive integers | 1 | 120764·5^33+368 | 1537 |

Here “natural” includes zero. Comparisons are free in the stated circuit model. Computing the norm residual before comparing it to zero adds one gate to each norm comparison-system count. Computing the two other residuals as well adds two further gates. Abbreviations are arithmetic registers, not unknowns; coefficients are fixed and not existentially quantified.

The verdict is a mathematical review of the new reductions **conditional on the explicitly inherited compiler, Pell-rank, and K215 calibration results and on one coherent authentic coefficient tuple**. This review does not independently rebuild those formal developments or certify a newly proposed compiler tuple. Under those inherited hypotheses, the arguments establish unbounded existential equivalence, not merely agreement on a finite search range. Their negations therefore yield the claimed ZFC-provable equivalence with Con(ZFC). Neither existence nor nonexistence of an actual solution has been established.

No counterexample to the reviewed reductions was identified. The optional split-weight and ratio-weight 24-integer forms were reviewed separately from the baseline, rather than silently inheriting the baseline's approval.

## 1. The twelve-positive-variable split-weight norm

Reference: `../norms/TWO_WEIGHT_PROOF.md` and the frozen `two_weight_norm12_*.json` circuits.

The final reviewed weights are

    W=2I(T+Raic), L=1+HW, M=2W,

not the earlier exploratory constants 8 and 4. The vanishing norm supplies a coherent triple of square roots and an auxiliary algebraic number satisfying

    S=Lu+HM tau+Hy,
    u²=G, tau²=A, f²=D,
    (Q−1)y²=Q(vf−b)²−1.

This is a factorization statement over an algebraic closure. It does not incorrectly assume that the three quadratic extensions are independent, and it remains true when roots coincide.

The weak transport bounds are obtained before using any reconstructed root. They supply positive data, X≥16, Y≥4096, R<c, a≥64, and Q≥3. Every conjugate of y, including imaginary branches, satisfies

    |y'| < (4/3)(v√D+b).

Dividing by √G>ac gives the three coefficients checked independently in the proof:

- the coefficient of TI is at most 11/8;
- the constant contribution is below 1/24;
- the coefficient of Ra i²c³ is at most 4355/3072<3/2.

Since TI≥1, these yield |y'|<(3/4)W√G. Separately,

    √G/√A < (1+66/1024)(65/64)=70850/65536<9/8.

Writing B=HW>36 therefore gives

    HM√A > (16/9)B√G > (7B/4+1)√G,

which strictly dominates every possible changed u and y term. A field automorphism flipping an irrational tau is impossible. Once tau is rational, the analogous argument makes u rational. Both become integers because their squares are integers.

The remaining integrality step is substantive: y is initially only rational. Recover f=(e−(Q−1)y²)/Baux, with Baux>0, so f is integral. The special Pell saturation lemma then makes y integral from

    m²V²−(m²−1)y²=1, m=ΔI≥2, V=vf−b∈Z.

Only after this step is reducing the linear relation modulo H justified; it gives the integral omitted main coordinate gamma. This avoids the common false assertion that rational points on integral Pell conics are automatically integral.

Completeness uses exactly

    r=gamma+W u+M tau+y.

Using the inherited formula with L tau would be wrong for this modified norm. The final manuscript and circuit use the corrected expression.

### Exact degree: tied terms are handled

The new weights cause leading-degree ties, so the original norm's “unique highest term” argument cannot simply be copied. With

    Z*=d* H*² R*² D*²,

the final weights give

    C0*=19Z*, K0pair*=256Z*²,
    U0*=(19²−256)Z*²=105Z*²,
    N*=105^4 Z*^8.

The other norm branch has strictly smaller degree. This is a uniform nonzero polynomial certificate, not just a modular diagnostic. It proves degree 1072 for the norm and 1081 for the product for every authentic fixed β>0.

## 2. Twenty-four unrestricted integers

References: `../integers/INTEGER24_PROOF.md`, `INTEGER24_SPLIT2_PROOF.md`, and `INTEGER24_RATIO_WEIGHT_PROOF.md`.

Six positive source ports use disjoint three-integer positivity parametrizations. The remaining six free coordinates supply odd i, odd s, square w, and unrestricted h,T,r. Thus the count is genuinely 6·3+6=24. Odd s supplies nonzeroness before its sign is known; it is not assumed positive.

The potentially circular proof order is resolved correctly:

1. The polynomial unit guard first gives the norm zero and common index/transport unit signs. Its parity identity is valid on arbitrary integer inputs.
2. Weak transport and odd nonzero s give Δ>R, G>4, |H|>6, and the strict interval 1<b<Q, even if w=0 and s<0.
3. With B=|H|Bnd>2, L=1+H Bnd satisfies |L|>B/2, including negative H. Thus |L|√G>|H|Bnd, while every auxiliary conjugate has magnitude below Bnd.
4. On the w=0 boundary, the first radicand is A=1. Its root is already integral, so the main-root separation works without the unavailable first-root dominance estimate. Pell saturation restores y in both Baux≠0 and Baux=0 cases. The restored gamma then makes the main norm congruent to 0 modulo H, contradicting its value 1.
5. Only now, with X≥16, the bound √G<4√A gives the second separation and restores all roots integrally for X>0.
6. The Baux=0 branch is handled without division. It forces T=0 and the integral equation Qb²−(Q−1)y²=1. The interval 1<b<Q puts y² strictly between b² and (b+1)², a contradiction.
7. Only after all roots and gamma are integral is the source negative-s theorem applied.

No division by a potentially zero radical occurs. Negative or coincident square-root branches cause no gap in the automorphism argument.

The signed-scale theorem's completeness needs more than odd i and square w separately: its canonical tableau also has popcount(R)=3 log₂(q)+2, giving v₂(Y)=3 log₂(q) and hence odd s. The reviewed source proves these restrictions simultaneously. They must remain explicit requirements when changing compiler coefficients.

The negative-s source proof was also read: it first restores p=R by signed auxiliary congruences, then forces the index signs and |Y|>2^R, and finally excludes both possible main-root signs modulo H. It is not an invocation of positive-s soundness while s is still negative.

### Optional lower-degree integer norm

Replacing the coefficient H L of tau by 2H Bnd preserves the boundary argument and gives, after X>0,

    √G<(175/128)√A<(3/2)√A,
    |L|√G+|H|Bnd < (31/16)|H|Bnd√A
                         <2|H|Bnd√A.

This proves the required signed first-root separation. The leading coefficient calculation has no cancellation: writing Z=H*Bnd*ell*, one obtains C0*=5d*Z², K0pair*=16d*²Z⁴, hence U0*=9d*²Z⁴ and

    N*=3^8 d*^8 Z^16.

Thus norm degree 2240 and product degree 2256 are correct. The variant costs one extra gate compared with the baseline norm. It is a degree/operation tradeoff, not a strict improvement on every measure.

### Further ratio-weight improvement: degree 1936

The separately audited final candidate keeps the same 24 integer coordinates and sets

    W=2[(iI)(1+5Rac)+v²], L=1+HW, M=2W.

This weight remains positive before the sign of s is known: ac>0 and iI=i²c²>0. Its central estimate is stronger and cheaper than the original absolute bound. The exact cancellation

    Dc²<GI²  iff  c²<I²

proves √D/√G<|I|/|c|, since |i|≥1 and |c|>1. Consequently

    |v|√D/√G ≤ |iT|c².

The inequality here must be non-strict when T=0; review identified this small manuscript strictness issue, and the final manuscript was corrected. No gap in the construction results, because the other bounds remain strict. Independently, √D<|a+2||I| and |a+2|<2|a| give

    D/√G < 2ac·iI,
    b/√G < 1+2Rac·iI.

Using 2|iT|c²≤iI+v² and Rac·iI>2 therefore gives the uniform bound

    |y'| < (W/2)√G.

It applies to all conjugates, to negative s or H, to signed or zero T, and on the X=0 boundary. With B=|H|W>8, |L|>B/2 gives main-root separation. The baseline A=1 argument excludes X=0 before any first-root estimate. Thereafter

    √G/√A < (273/256)(33/32)=9009/8192<9/8,
    |L|√G+|H||y'| < (117/64)B√A < 2B√A.

Thus the first-root separation, saturation, T=0 exclusion, and subsequent negative-s theorem all apply in their correct order. Completeness uses r=gamma+W u+M tau+y and adds no restriction on canonical witnesses.

The degree audit must again account for tied terms. Put Z*=d*H*²R*²D*², now of degree 240. Then

    (dV0)*=100Z*, (da0)*=400Z*, (H²e)*=Z*,
    C0*=499Z*, K0pair*=160000Z*²,
    U0*=(499²−400²)Z*²=89001Z*²,
    N*=89001^4 Z*^8.

This is equivalent to the manuscript's (99·899)^4 d*^8 H*^16 b*^16 certificate. The earlier split-weight 3^8 certificate would be wrong here because H²e is no longer lower degree. The corrected generator and actual packet use the proper certificate. Norm degree 1920, product degree 1936, and SOS degree 3840 follow uniformly. The product costs 168 gates; the comparison system costs 163. This is a further degree/operation tradeoff, not a replacement for the cheaper 163-operation baseline product.

## 3. Nine-variable Jones specialization

Reference: `../nine/IMPROVEMENT_PROOF.md`.

### Same polynomial, much smaller circuit

The exponent identity

    B^(5T−Σα_j5^j)=B^T(B^T)^(4−|α|)Π(B^(T−5^j))^α_j

is a polynomial identity, including B=0. Reusing fifth powers and complement powers, and applying multivariate Horner evaluation, therefore preserves the digit polynomial exactly. The geometric-sum factorization is likewise division-free and exact. The 1616-gate version computes the same package-18 polynomial that previously used 20531 gates; this is not merely a new polynomial with the same zero set.

### Final coefficient-recipe folding

A further exact optimization gives the final counts 1485 for the unchanged package-18 polynomial, and 1542 natural / 1537 positive for the new majorants. These replace the larger independent-leaf counts as the best circuits in the reviewed bundle. Degrees and zero sets are unchanged.

All 346 coefficient records were independently checked as sparse integer polynomials in the four fixed compiler ports, not compared merely by their numerical residues or hashes. Exactly 260 records are literal integers; all records together have 98 distinct recipes. Equal nonliteral recipes may therefore share a leaf, and literal recipes may become their actual integer leaves, for every authentic compiler tuple. The specialized circuits have 66 fixed leaves: the two index constants and 64 distinct nonliteral coefficient recipes. The full 346-record specification remains available for index construction.

The optimization cannot be used while pretending those 346 leaves are arbitrary independent parameters. It is valid here because their exact recipes are part of the concrete construction. An additional 192 recipe-bound generic-versus-specialized comparisons, across all six variants, verified the emitted nodes and the claimed operation counts. The unchanged Horner/distributivity identities supply the universal algebraic justification; modular examples alone would not do so.

### New natural-domain majorants

The new sign-erased construction requires nonnegative inputs. It is not claimed valid over all unrestricted integers. The key subtlety is e≥0: this follows from the full index-digit expression with z+c_alpha>0, **not** from positivity of sparse correction coefficients, which may be negative.

All inputs to the sign-erased R expression are consequently nonnegative before any ratio, square, or margin condition has been established. Replacing subtraction by addition gives Rbar≥|R|. The subsequent bars dominate |P|,|K|,|A|,|C|,|D|,|E|,|F|,|Gp|,|H| by direct induction. This is noncircular.

For abar≥|a| and bbar≥|b|, the inequality

    |(a²−1)b²+1| ≤ (abar²+1)bbar²+1
                   ≤ ((abar+1)bbar+1)²

holds. The second difference is exactly

    2abar·bbar²+2(abar+1)bbar≥0.

It proves the required radical bounds for V0 and V1; the extra factor 2 in V1 is harmless and provides a simple degree certificate.

### The finalizer does not admit sign or degeneracy exceptions

J=4A−5 is never zero at integral A. F=0 would force A=0 and E=±1, whereas E=iJDC² would then be divisible by 5. Thus d=(JF)²>0 unconditionally.

A zero of the four-factor norm gives r0+V0 r1 rational. If this sum is nonzero, squaring isolates both roots as rationals, hence integers. If it is zero, the strict bound |r0|<V0 implies |r1|<1, so the integral radicand a1 is zero and then a0 is zero. This covers initially negative radicands, repeated square classes, and zero roots.

After root integrality, Z=c+V0V1+r0+V0r1≥c+1>0. Since n≥0 and c≥0, the equation

    dn+c=d(2m−1)Z

forces m>0, and also forces d|c. Conversely, the four ratio conditions give an explicit integral n≥1. The natural-domain sign constraint is essential precisely here and is retained. Shifting all nine coordinates by one gives the stated positive-domain form, not an unrestricted-integer form.

The final degree calculation correctly retains the tied leading terms: their difference is 2^128−2^126=3·2^126, and the final subtraction has lower degree. Hence exact degree 120764·5^33+368 and diagonal leader 9·2^252 are justified uniformly, independently of fixed coefficient values.

## 4. Low-degree lifts and final report text

The new low-degree files and `../integers/LOW_DEGREE_PROOF.md` were additionally reviewed. They give sums of squares in 51, 42, and 36 unrestricted integers at exact degrees 4, 6, and 8, respectively. Their residual systems have 30, 21, and 15 equations. Removing the retained s guard deletes three auxiliary parameters, not two, because the old s register itself remains as the odd affine parameter.

The potentially delicate quartic case exposes quotients o,j rather than an integer T. For negative s, the first/main Pell classification and index equations already provide the required growth bound |c|>BΔ² before any use of T. The ordinary strong-rank theorem then supplies f²≡1 modulo |c|. Consequently

    of+R=(j+1)c,
    o+Rf=f(of+R)−o(f²−1)

prove that T=(o+Rf)/c is integral even when c<0. Only after restoring this signed T is the source negative-scale theorem invoked. Thus the proof does not assume positive s in order to establish positive s. The sextic and octic restore their normalized or ordinary strong equations through polynomial register identities, with the first-root shear an integer affine bijection; no additional positivity assumption is inserted.

An independent SymPy implementation verified all 66 residual substitutions exactly, the one removed guard in each parent, source-parent hashes, all variable counts and liveness, and the degree certificates 1, 4β², and 4β⁶. These are exact symbolic identities, not sampled equality tests. Source rank and compiler semantics remain inherited dependencies.

The text of the delivery-root `report.tex` was reviewed for mathematical transcription, metrics, and scope. Its norm, integer, Jones, and low-degree claims match the reviewed artifacts. The requested precise denominator argument in the short saturation proof and explicit square conditions in the Jones converse were added and their corrected text was verified. This was a text review, **not** a claim that the report was compiled, rendered, or visually inspected. The report's new coefficient geometry and its corresponding source-calibration work remain outside this review's independent scope.

## 5. Implementation evidence and limits

The independent scripts in this directory were written separately from the new builders.

- `check_novel_norms_independent.py`: 96 exact signed assignments for each of twelve norm packets, 1152 in total, plus 3888 signed and zero-scale boundary fixtures for the ratio weight. It multiplies the eight formal conjugates directly in a separately implemented quadratic-algebra representation, checks the norm/parity/finalizer identities, and audits all gates and input ports for liveness. Degenerate and negative radicands occur in the algebra fixtures, though they are excluded by semantic bounds on actual solutions.
- `check_nine_improvements_independent.py`: 64 full old-versus-new modular DAG comparisons, 96 positive-shift comparisons, 256 exact sign-erased-majorant fixtures, 1000 explicitly constructed finalizer witnesses, all 346 exact coefficient-alias identities, and 192 recipe-bound comparisons of generic versus specialized circuits.
- `check_low_degree_new_independent.py`: exact SymPy replay of all 66 changed residuals and their degree certificates.
- Receipts are `NOVEL_NORM_INDEPENDENT_CHECKS.json`, `NINE_IMPROVEMENTS_INDEPENDENT_CHECKS.json`, and `LOW_DEGREE_NEW_INDEPENDENT_CHECKS.json`.

One concrete metadata defect was found and corrected during review: the natural-domain Jones packets initially recorded a register-name dictionary instead of the nine-variable list because a local name was overwritten. Their polynomial nodes were unaffected. The builder was corrected and all packets regenerated before the final replay.

These finite checks validate implementation details. They cannot establish the universal separation inequalities, the inherited compiler semantics, or the truth of Con(ZFC). Those distinctions must remain visible in the final presentation. No globally minimal equation, new eleven-variable construction, or newly kernel-checked end-to-end ZFC theorem is claimed.

# Independent review: encoded-gap counting continuation

**Verdict: ACCEPT within the stated arithmetic scope.** No mathematical defect or required correction was found in the frozen counting proof. The exact formulas, endpoint conventions, sharp direct and inverse envelopes, and distinctions between multiplicities and represented totals are valid. This is an independent verification of the supplied candidate, not a claim of independent discovery or novelty.

Review date: 4 October 2026. This review is a separate, unnumbered artifact. It changes neither the reviewed packet nor its dependency.

## 1. Exact source binding and method

The reviewed directory is `native-gap-counting-continuation-20261004`. Its bindings are:

- `PROOF.md`: `dbc5c8e1cc692f734eaf795a57d081af242469ad41fdcbcdbed0ab5324d55246`
- `MANIFEST.json`: `0a660b083eb7c381eb3af1d31cb992dee3ccd2f77a0f473cffb062314aae4781`
- Primitive-input dependency, `native-gap-halting-continuation-20261004/PROOF.md`: `8cc5911e528d0555ee89fe63f0e30b8a3eac4a32e3e4237ee9b00a38107a7d1b`

Every manifest entry's byte length and SHA-256 was checked. All six counting-packet files and the dependency proof were verified unchanged after the independent run. Source references below use the frozen counting proof's line numbers.

The packet's Python source and recorded results were read as inert text, not executed, imported, or used as an oracle. The independent checker instead derives primitive scales from the least common multiple of reduced coordinate denominators, then checks a separate exhaustive positive-triple enumeration. No author/upstream code, counter interpreter, physical simulation, accepting schedule, or Lean execution was used. No external sequence identification was attempted or needed.

The source makes its counting results conditional on the primitive theorem. Section 2 below independently reconstructs that elementary theorem directly from the coordinate fractions. Consequently this review of counting does not rely on the dependency's Pell modules, halting construction, or physical transport.

## 2. Encoding, minimal scale, and unique positive multiples

Source: lines 7–28; dependency Section 6.

Write

    q(a) = 1/20 + 1/(10·2^a) = (2^a+2)/(20·2^a).

These fractions are strictly decreasing for integer a≥0, so the normalized first and third gaps recover a and b uniquely. They satisfy 1/20<q(a)≤3/20. Therefore the middle coordinate 1−q(a)−q(b) is at least 7/10 and is positive for every counter pair.

Let e(a) be the denominator of q(a) in lowest terms. Direct reduction gives

    e(0)=20, e(1)=10;
    e(a)=2^(a+1)       if a≥2 and a≡3 (mod 4);
    e(a)=10·2^a        otherwise, for a≥2.

For a≥2, the numerator has exact 2-adic valuation one. Its only possible further common factor with the denominator is 5, and 5 divides 2^a+2 exactly when a≡3 (mod 4). This proves the reduction, including its exceptional small cases.

An integer total D gives three integer coordinates precisely when both e(a) and e(b) divide D: the middle coordinate is then D minus two integers. Thus the exact smallest total is

    d(a,b)=lcm(e(a),e(b)).

This immediately gives the displayed classification in the source. For maximum m≥2 the largest power of two in either endpoint denominator is 2^(m+1); the factor 5 disappears exactly when both counters are 3 modulo 4. The cases m=0,1 give 20, 10, 20 as stated. In every case d(a,b)≥2^(m+1).

At total d the three integer coordinates have gcd one: a common factor greater than one would produce a smaller integer total with all coordinates integral, contradicting the least common multiple. Every permissible total is a unique positive integer multiple of d, and its triple is the same multiple of the primitive triple. Distinct ordered counter pairs cannot overlap because decoding is unique. Hence

    A(N)=Σ_(a,b≥0) floor(N/d(a,b))

counts triples exactly once. The lower bound on d makes the nonzero part finite. Ordered pairs are essential: exchanging a and b generally exchanges the first and third gaps and gives a different triple.

Small primitive examples are (3,14,3) at (0,0), (1,8,1) at (1,1), (3,15,2) at (0,1), and (1,14,1) at (3,3). Their totals are respectively 20, 10, 20, and 16.

## 3. Exact floor and digit formulas

Source: lines 30–56.

There are (m+1)^2−m^2=2m+1 pairs with maximum m. Assigning all of them provisional scale 10·2^m yields F₂(floor(N/10)). The pair (0,0) exchanges provisional total 10 for 20, while (1,1) exchanges 20 for 10; the two floor corrections cancel for every N, not just asymptotically.

All remaining changes occur at maximum m=4k+3. Among the k+1 possible special counters 3,7,…,4k+3, exactly 2k+1 ordered pairs have this maximum. Each changes its total from 80·16^k to 16^(k+1). Therefore, for every integer N≥0,

    A(N)=F₂(floor(N/10))+F₁₆(floor(N/16))−F₁₆(floor(N/80)),
    F_b(n)=Σ_(k≥0)(2k+1)floor(n/b^k).

The floor nesting identity used here is exact for positive integer divisors. In particular, the correction does not assume that special pairs with large counters have zero floor contribution.

For digits n=Σ_j d_j b^j, put s=Σ_j d_j and w=Σ_j j d_j. Expanding the floors gives a coefficient

    S_j=Σ_(k=0)^j (2k+1)b^(j−k)

for digit d_j. Its initial value is S₀=1 and its recurrence is S_j=bS_(j−1)+2j+1. Substitution verifies the unique solution

    S_j=[b(b+1)b^j−(3b−1)]/(b−1)^2−2j/(b−1).

Multiplying by the digits and summing proves the source identity

    F_b(n)=[b(b+1)n−(3b−1)s_b(n)]/(b−1)^2−2w_b(n)/(b−1).

This argument includes n=0 by empty digit sums and applies to every integer base b≥2. No named digital-sum theorem is needed.

## 4. Shell multiplicity and distinct totals

Source: lines 58–72.

For N≥1, floor(N/d)−floor((N−1)/d) is one exactly when d divides N. Thus each primitive shape whose total divides N contributes one, and only one, triple to J(N).

Let v=v₂(N). If 5 divides N, the baseline divisors have maxima 0≤m≤v−1 and their weights sum to Σ_(m=0)^(v−1)(2m+1)=v². For every special replacement, both old and new scales divide N under the same condition v≥4k+4, so their corrections vanish. This includes v=0, when the baseline sum is empty.

If 5 does not divide N, no baseline scale divides N. The available new special scales are precisely 16^(k+1) with 0≤k<floor(v/4). Their weights sum to floor(v/4)². Consequently

    J(N)=v₂(N)²                    if 5 divides N,
         floor(v₂(N)/4)²           otherwise.

A shell is nonempty precisely when 10 divides N or 16 divides N. Since lcm(10,16)=80,

    B(N)=floor(N/10)+floor(N/16)−floor(N/80)
        =(3/20)N+O(1).

B counts each total once. A counts all its J(N) triples. The density 3/20 is therefore not interchangeable with the triple slope.

## 5. Reciprocal sum and the global error bound

Source: lines 74–99.

Absolute convergence follows from d(a,b)≥2^(max(a,b)+1). The low-counter correction still cancels, and the special replacement gives

    ρ=(1/10)Σ_(m≥0)(2m+1)/2^m
       +(1/16−1/80)Σ_(k≥0)(2k+1)/16^k
      =3/5+68/1125=743/1125.

The elementary series identity Σ(2k+1)x^k=(1+x)/(1−x)^2 follows by multiplication by 1−x. As an independent constant check, the shell formula gives the same rational mean: the v₂=v, 5-divisible class has density 1/(5·2^(v+1)), and its complement within v₂=v has density 4/(5·2^(v+1)). Grouping v in blocks of four yields the same 3/5+68/1125. The limiting argument is already justified by the reciprocal-sum proof and the error estimate, so this cross-check is not used in place of convergence control.

Because the reciprocal sum converges and only finitely many floors are nonzero,

    E(N)=ρN−A(N)=Σ_(a,b≥0){N/d(a,b)}≥0.

For N≥1 and L=floor(log₂N), the (L+1)² terms with maximum at most L contribute strictly less than (L+1)². For the remaining terms, use {x}≤x and the primitive lower bound:

    tail ≤ N Σ_(m=L+1)^∞ (2m+1)/2^(m+1)
         = N(2L+5)/2^(L+1) < 2L+5.

Adding gives exactly

    0≤E(N)<L²+4L+6.

The strict inequality is valid even at powers of two. In particular, A(N)/N→ρ. This is growth in the total bound N, not the proportion among all positive integer triples with total at most N; the latter universe has binomial(N,3) elements.

## 6. Divisibility, square jumps, and sharp direct constants

Source: lines 101–114.

Put N_M=10·2^M with M≥1. The low-counter totals 10 and 20 divide N_M. For all larger maxima, both normal totals 10·2^m and special totals 2^(m+1) divide N_M exactly when m≤M. Thus every pair in the (M+1) by (M+1) square contributes to the shell, and no other pair does:

    J(N_M)=(M+1)².

**The cutoff is divisibility, not size.** For example, at M=1 the pair (3,3) has d=16<20=N₁, but 16 does not divide 20. More generally a special total with m>M can be at most N_M only when m−M is 1 or 2; it still cannot divide N_M. The source states the correct distinction explicitly. Discarding all such floor contributions would give incorrect cumulative counts.

In the fractional-part formula for E(N_M), all terms with maximum at most M vanish. The same tail estimate, now at M, gives the fully explicit sufficient bound

    0≤E(N_M)≤10M+25.

This bound remains valid when some tail totals are below N_M, because it bounds their fractional parts by N_M/d rather than setting their floors to zero. The exact jump relation is

    E(N_M−1)=E(N_M)+(M+1)²−ρ=M²+O(M).

The general upper bound gives limsup at most one after division by (log₂N)². The N_M subsequence gives liminf zero, and the N_M−1 subsequence gives limsup at least one. Hence the exact constants are

    liminf E(N)/(log₂N)²=0,
    limsup E(N)/(log₂N)²=1.

These imply failure of a uniform o(log²N) error and of an expansion E(N)=c(log₂N)²+o(log²N) with one constant c. No broader assertion about possible correction functions or asymptotic expansions is required or certified.

## 7. Recomputed four-class error formula

Source: lines 116–134.

For M≥3 write M−3=4q+t, 0≤t≤3, c=2^t, and h=floor(5c/16). The three floor-formula arguments are exactly 2^M, 5c·16^q, and c·16^q. In base 16, 5c has low digit 5c−16h and high digit h, whereas c is one digit. Therefore the digit-sum difference is δ=4c−15h, and the weighted difference is qδ+h.

The four (δ,h) pairs, in order t=0,1,2,3, are (4,0), (8,0), (1,1), (2,2). Since F₂(2^M)=6·2^M−2M−5, substitution gives

    E(N_M)=2M+5+(47/225+2q/15)δ+2h/15.

Using q=(M−3−t)/4 and r=M mod 4 reproduces every coefficient:

| r | α_r | β_r |
|---|---:|---:|
| 0 | 34/15 | 1261/225 |
| 1 | 61/30 | 2329/450 |
| 2 | 31/15 | 1189/225 |
| 3 | 32/15 | 1223/225 |

Thus E(N_M)=α_rM+β_r. The two small cases are separately valid: A(20)=6 gives E(20)=1622/225, and A(40)=17 gives E(40)=2119/225. They agree with the r=1 and r=2 rows. The left-neighbor formula follows by adding (M+1)²−ρ without further rounding or floor conventions.

## 8. Multiplicity inverse and its sharp constants

Source: lines 136–178.

For rank n≥1, D_n=min{N≥0:A(N)≥n} exists because the primitive total 10 supplies at least n triples by total 10n. Thus

    n/ρ≤D_n≤10n,
    A(D_n−1)<n≤A(D_n).

The first lower bound follows from A(N)≤ρN, so the inverse deviation is nonnegative. Using the defining strict inequality and the error formula gives

    ρD_n−n<ρ+E(D_n−1).

All D_n are at least 10, so E(D_n−1) is in the domain of the global estimate. Since log₂(D_n−1)≤log₂n+log₂10, this establishes both

    D_n=(1125/743)n+O(log²n)

and the sharper global upper envelope

    D_n−n/ρ ≤ (1/ρ)(log₂n)²+O(log n).

This coefficient does not follow merely from an unspecified O(log²n) bound; it follows from carrying the coefficient one in the direct error estimate through the displayed inequality.

Let the first and last ranks of the N_M shell be f_M=A(N_M−1)+1 and l_M=A(N_M). The shell is nonempty and both inverse values are exactly N_M. There is no off-by-one ambiguity:

    D_(f_M)−f_M/ρ=[E(N_M)+(M+1)²−1]/ρ
                =[M²+(2+α_r)M+β_r]/ρ,
    D_(l_M)−l_M/ρ=[α_rM+β_r]/ρ.

Both ranks equal ρ·10·2^M−O(M²), so their base-two logarithms are M+log₂(10ρ)+o(1). The last ranks therefore give normalized liminf zero, and the first ranks give normalized limsup 1/ρ. Combined with the global bound,

    liminf [D_n−n/ρ]/(log₂n)²=0,
    limsup [D_n−n/ρ]/(log₂n)²=1125/743.

This is the inverse with each total repeated J(N) times. Separately, B(N)=(3/20)N+O(1) gives the inverse of distinct represented totals as (20/3)n+O(1).

## 9. Domains and endpoint checks

- A(0)=0 and all floor/digit formulas include zero. J and v₂ are used only for N≥1. The logarithmic global estimate is likewise stated only for N≥1.
- The subsequence divisibility argument requires M≥1. At M=0, the low-counter pair (1,1) has maximum above M but d=10 divides N₀=10; the frozen proof correctly excludes that case. Some numerical formulas happen also to extend to M=0, but that coincidence must not be substituted for the stated proof.
- F_b is defined for integer b≥2 and integer n≥0. Empty sums in the shell formula, particularly v₂(N)=0 or v₂(N)<4, give zero correctly.
- The first counts are A(9)=0, A(10)=1, A(15)=1, A(16)=2, A(19)=2, A(20)=6, A(40)=17. The first inverse totals are 10,16,20,20,20,20.
- At M=1 the first and last shell ranks are 3 and 6, both at total 20. Thus the first/last distinction is already nontrivial in the smallest permitted subsequence case.
- All sharp normalized constants use log base two. Rank one, where log₂1=0, is irrelevant to the limits; the all-rank inequalities above remain valid.

## 10. Independent executable evidence and limits

The companion `check_independent.py` uses only the Python standard library and exact arithmetic. It checks source identity before and after, reads packet programs as bytes only, and prints JSON to stdout without modifying them. Unlike the packet's gcd construction, its main primitive oracle is the least common multiple of the normalized coordinate denominators. A second path exhaustively enumerates ordinary positive triples and decodes their endpoints.

The completed run in `checks.json` reports PASS for:

- All 4,225 counter pairs with 0≤a,b≤64: denominator-derived scale classification, positivity, primitive gcd, uniqueness of shape, exact decoding, and the scale lower bound
- All 669,920 positive triples of total at most 160, checking exact membership and unique integer scaling
- Every total 1 through 250,000: independently sieved shell multiplicity, cumulative floor count, distinct-total count, and the nonnegative strict error envelope
- All 164,979 inverse ranks represented through total 250,000, checked in their tied shell blocks; A(250000)=164979 and B(250000)=37500
- All 63,519 digit-identity cases with bases 2 through 32 and arguments 0 through 2,048
- Exact four-class errors, square jumps, left-neighbor errors, and both inverse endpoint identities for M=1 through 400
- Independent denominator-derived counts at N_M and N_M−1, independent binary-search inverse endpoints, and the exact divisibility cutoff for M=1 through 48
- Explicit examples and 288 checked instances of special pairs whose primitive scale lies below N_M despite maximum counter above M, without divisibility
- Independent rational evaluations of 743/1125 and 3/20, and a finite reciprocal sum bounded against its proved infinite-tail bound

These finite checks do not establish the all-input formulas or limiting assertions by themselves. Sections 2–8 supply the mathematical arguments. Conversely, the review does not promote any recorded finite test in the author packet into an independent execution result.

## 11. Scope and disposition

All conclusions count encoded positive integer initializations. No program, halting predicate, time horizon, physical schedule, or Diophantine witness multiplicity enters A, J, B, or D_n. Nothing here counts halting inputs or resolves an OEIS open problem. The packet contains no theorem of that kind, and this review grants none.

**Disposition:** the frozen packet is mathematically sound as stated. No source amendment is requested. Preserve the distinction between size and divisibility at N_M, and preserve multiplicity in every use of the inverse result.

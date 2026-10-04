# Arithmetic review of the primitive-Pythagorean rotation family

4 October 2026. This is a fresh arithmetic proof and review, not a geometric or physical frontend implementation. The prior PROOF.md was used only to obtain the displayed fifteen POWER equations. The two relevant theorem statements in the inert Pell source were also read as text; no inherited code, Lean build, simulator, or old checker was run.

## Result

Fix integers a,b,c with a²+b²=c², gcd(a,b,c)=1, a,b nonzero, c>1. Put λ=(a+ib)/c and ε=sign(b). The proposed denominator, exponent-factorization, bounded-extraction, and orientation clauses are correct, including negative a and composite c. For a fixed list of M nonzero rational tangencies, and a quadratic integer radius deficit, the stated conjunction has 1+80M positive witnesses and 1+43M equations. Its sum-of-squares polynomial has exact total degree 12 when M≥1. The arithmetic theorem is conditional on the geometric criterion being exactly the stated radius-and-inverse-orbit criterion; this review does not establish that geometric criterion.

## 1. Exact joint denominators

Primitivity implies gcd(a,c)=gcd(b,c)=1: a prime dividing either pair would also divide the third entry. Also c is odd, since c even would force both a and b even by reduction modulo 4.

Let α=a+i|b| and αⁿ=Cₙ+iSₙ. For each prime p dividing c, work in the ring (Z/pZ)[i], where i²=−1. We have

    α² = 2aα,
    αⁿ = (2a)^(n−1) α   for n≥1.

Indeed, |b|²≡−a² modulo p. Both 2a and the two coordinates of α are nonzero modulo p, since p is odd and p does not divide ab. Consequently neither Cₙ nor Sₙ is divisible by p. Thus

    gcd(Cₙ,Sₙ,cⁿ)=1.

Since λ^(−n)=(Cₙ−iεSₙ)/cⁿ, its least common positive denominator is exactly cⁿ. At n=0 the numerator is (1,0), the denominator is 1. This also proves that λ has infinite order. No assertion about Gaussian prime factorization, squarefreeness of c, or c being prime is needed.

For any integer U,V and positive Q, equations U=hu, V=hv, Q=hq with h,q positive, together with A₁u+A₂v+A₃q=1 for signed Aᵢ, force h=gcd(U,V,Q) and gcd(u,v,q)=1. Conversely those canonical values admit Bezout witnesses. The positive q is the joint denominator: if d clears both coordinates, q divides du and dv; multiplying the Bezout equation by d gives q dividing d. When U=V=0, these same equations force u=v=0, q=1, h=Q. Zero coordinates require no exception.

## 2. Composite-base exponent extraction

For every positive integer q and every integer c>1 there is a unique n≥0 and r>0 with

    q=cⁿr,   c does not divide r.

Take the largest n with cⁿ dividing q. Existence is finite because cⁿ≤q whenever cⁿ divides q. If n<n′ were two such exponents, r would be divisible by c, contradiction. This is a maximal whole-base divisibility exponent; for composite c it should not be called an additive valuation.

The equations r=ck+s and s+t=c, with k natural and s,t positive, express exactly c∤r: they say 1≤s≤c−1 and use the ordinary Euclidean quotient and remainder. A remainder may share prime factors with composite c; that causes no problem. In particular q=cᵐ forces n=m and r=1.

## 3. Extraction with a positive ordinary-power base

Put P=cⁿ, B=4P+2c+1 and H=a+|b|B. Since |a|<c and a is integral,

    H ≥ B−(c−1) = 4P+c+2 > 2.

Thus POWER(H,n) meets its positive-base hypothesis even when a<0. The first base c also meets that hypothesis.

The norm identity gives |Cₙ|,|Sₙ|≤P. Polynomial substitution i↦B modulo B²+1 gives

    Hⁿ ≡ Cₙ+BSₙ  (mod B²+1).

Conversely, suppose integers C,S satisfy |C|,|S|≤P and Hⁿ−C−BS is a multiple of B²+1. Write dC=C−Cₙ and dS=S−Sₙ. Their corresponding linear combination is a multiple of B²+1, but

    |dC+B dS| ≤ 2P(B+1) < B²+1,

because the difference on the right is

    8P²+12Pc+4P+4c²+4c+2 > 0.

Therefore dC+B dS=0. Since |dC|≤2P<B, this forces dS=dC=0. A signed quotient κ in Hⁿ−C−BS=κ(B²+1) imposes no unwanted sign restriction. The four bound slacks must be natural, so equality is allowed. At n=0 we obtain P=1, H⁰=1, C=1, S=0, κ=0.

## 4. Strict acceptance and its orientation

For a nonzero rational tangency pⱼ, write the input-to-tangency ratio ηⱼ=(Uⱼ+iVⱼ)/Qⱼ with integer Uⱼ,Vⱼ and positive Qⱼ. Reduce it by the gcd equations above, and extract qⱼ=c^nⱼ rⱼ and Cⱼ+iSⱼ=(a+i|b|)^nⱼ. The exact-denominator lemma proves

    ηⱼ is λ^(−m) for some m≥0
    iff rⱼ=1, uⱼ=Cⱼ, vⱼ=−εSⱼ.

Hence the equation

    δ²+(rⱼ−1)²+(uⱼ−Cⱼ)²+(vⱼ+εSⱼ)²=Jⱼ,

with Jⱼ positive and δ natural, enforces strict avoidance of this forbidden orbit on the boundary δ=0 and imposes no exclusion when δ>0. It rejects exponent zero correctly. If b<0 the final term is (vⱼ−Sⱼ)², which is the required inverse orientation. Conjoining the clauses for a fixed finite list of tangencies is precisely avoidance of their finite union of inverse orbits. Repeated tangencies or inverse-orbit overlap merely add redundant clauses.

This requires nonzero pⱼ. Division by a zero tangency is undefined. The ordinary positive-radius geometric setting supplies this prerequisite, but the arithmetic statement should say it explicitly.

## 5. POWER equation hypotheses

The inherited fifteen-equation module shifts e to k₀=e+1≥1 and asks for B₀^k₀=B₀·out. Reading the two displayed Pell theorem statements confirms the required correspondence: the first nine equations enforce the nonzero-index Matiyasevic branch, and the last six enforce the positive-base, positive-index branch of eq_pow_of_pell. In particular y≥k₀, w≥max(B₀,k₀), M>B₀·out, and the two-sided natural congruence witnesses all remain present.

The Pell parameter A≥2 satisfies

    A²=1+((w+1)²−1)(wg)².

With w≥B₀≥2 and g positive, this forces A>w≥B₀, so A−B₀ is an ordinary nonnegative integer and agrees with the natural subtraction in the theorem. Conversely the constructive theorem's positive-index witnesses have g>0, positive Pell coordinates, positive quotient qv, and positive qb. The congruence t≡k₀ modulo 4y with 1≤k₀≤y excludes t=0. Every signed congruence quotient is representable as a difference of two naturals. Thus the displayed positive-domain specialization and exponent-zero shift do not introduce the new edge-case failure under consideration. This is a theorem-specialization check, not a fresh formal proof of the Pell theorems.

## 6. Exact finite counts and degree

Use one shared natural δ (one positive leaf after subtracting 1). Per tangency there are:

- Six natural variables: n,k,L_C,H_C,L_S,H_S
- Six positive variables: h,q,r,s,t,J
- Eight signed variables: u,v,A₁,A₂,A₃,C,S,κ, each represented by two positive leaves
- Two POWER modules, each with 26 positive leaves and 15 equations

Thus there are 80 positive witnesses per tangency. Per tangency the outer equations are four gcd/fraction equations, three denominator-factor equations, four bounds, one congruence, and one strict-acceptance equation: thirteen, in addition to the thirty POWER equations. With one shared radius equation the totals are 1+80M witnesses and 1+43M equations. These counts exclude any additional parameter-validity or input-decoding relations. Three-input Cantor decoding, if desired in the same format as the source, would add four witnesses and two equations.

For fixed a,b,c and fixed rational pⱼ, the rational-fraction input forms are linear after clearing fixed denominators; assume the radius residual is quadratic. The extraction base B and ordinary-power base H are affine in the independent POWER output P. Each outer residual then has degree at most 3, while each expanded POWER residual has degree at most 6. The degree-six leading term of the thirteenth module residual is −w⁴g². Its square contributes w⁸g⁴. The highest homogeneous part of a sum of real polynomial squares cannot cancel identically, so the final degree is exactly 12 for M≥1.

If M=0, there are no POWER modules and the construction does not have exact degree 12; in the quadratic-radius case its unpadded degree is 4. The construction is a fixed finite-arity family for each fixed tangency list. It is not a single constant-arity frontend accepting an arbitrarily long list.

## 7. Fresh checks and limits

check_arithmetic.py independently enumerated 256 signed, ordered primitive triples with c≤200, and checked 5,376 powers at n=0 through 20 using exact integers. Composite hypotenuses included 25,65,85,125,145,169,185. All denominator, congruence, positivity, uniqueness-bound, and whole-base factorization checks passed.

check_symbolic_template.py is a new standard-library sparse-polynomial checker. For the negative-a, negative-b example (−16,−63,65), it explicitly forms the fifteen module residuals twice, the fourteen outer residuals, all positive-domain adapters, and the sum of their squares. It confirms 81 positive witnesses, 44 equations, degree 12, and coefficient 1 on each module's w⁸g⁴ monomial. It uses formal linear U,V,Q and a toy quadratic radius residual solely to check arithmetic degree and counts. This is not an implementation of the physical input frontend, nor a gate-count claim for a general geometry. Finite checks supplement the proof; they do not replace it.

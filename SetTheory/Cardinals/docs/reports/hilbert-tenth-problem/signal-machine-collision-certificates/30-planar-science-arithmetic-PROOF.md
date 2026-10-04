# A positive-integer certificate for arbitrary rational elliptic backward orbits

4 October 2026. Conventional exact proof and an explicit polynomial formula, not a proof-assistant build or an arithmetic-DAG claim. All prior files are preserved. The only substantial inherited arithmetic theorem is the completely displayed POWER module from Report 59; its pinned Pell theorem statements were inspected as text, and no upstream program was executed.

## 1. Statement, scope, and input convention

Fix an infinite-order elliptic matrix A in SL₂(Q), and a finite nonempty list of nonzero rational points z₁,…,zⱼ. Write

    tr(A)=p/q,  gcd(p,q)=1,  q>0,  |p|<2q.

The infinite-order hypothesis is exactly q≥2 in this elliptic range: rational traces of finite-order elliptic matrices are the integers −1,0,1. All matrix, trace, contact, and ellipse data in the certificate are fixed coefficients, not witnesses.

An input is a rational point

    x=(X/N,Y/N),  X,Y integers, N a positive integer.

No coprimality is required. To make all *inputs* positive integers too, take five positive inputs a₁,a₂,a₃,a₄,a₅ and set X=a₁−a₂, Y=a₃−a₄, N=a₅. This covers every rational point, although the encoding is not unique. More generally X,Y,N may be fixed integer linear expressions in any fixed number of positive input variables, provided N>0 on that input domain. In particular, a physical compiler's three positive gaps may supply these forms without extra witnesses.

**Orbit-complement theorem.** There is an explicit polynomial with integer coefficients, obtained below as a finite sum of squared residuals, such that

    x is outside every {A^(−n)zⱼ : n≥0}
    iff the polynomial vanishes for some 81J ordinary positive integer witnesses.

The displayed formula has 44J residual equations and exact total degree 12. Here J is the fixed length of the contact list. There is no claim of a uniform fixed arity when an arbitrarily long list is part of the input.

**Strict-kernel corollary.** Suppose a rational positive definite matrix Q, a positive rational r², and the contacts zⱼ give the exact geometric predicate

    xᵀQx<r², or xᵀQx=r² and x avoids all backward contact orbits.

Then this predicate has the displayed positive-integer formula with 1+81J witnesses, 1+44J residual equations, and exact degree 12. The strict-kernel classification constructs precisely such data for any bounded open rational convex polygon containing 0 and any infinite-order elliptic rational A. The present arithmetic proof does not change that geometric theorem or claim a physical realization by itself.

The result extends the Gaussian-coordinate extraction in Report 59. Rational conjugacy to a Euclidean rotation is neither used nor assumed. For example tr(A)=1/2 is allowed.

## 2. A rational contact basis and its exact denominators

Put B=A⁻¹ and, separately for each nonzero rational contact z, define

    S=[z,Bz],     C=[[0,−1],[1,p/q]].

The columns are independent: dependence would give a real eigenvector of B, impossible for a nonreal spectrum. Cayley–Hamilton gives BS=SC. Thus

    S⁻¹ A^(−n)z=Cⁿe₁.

Let U₋₁=0, U₀=1 and Uₖ=(p/q)Uₖ₋₁−Uₖ₋₂ for k≥1, taking U₁=p/q. Direct induction gives

    C⁰e₁=e₁,
    Cⁿe₁=(−Uₙ₋₂,Uₙ₋₁)  for n≥1.

For k≥0 put Vₖ=qᵏUₖ. Then V₀=1, V₁=p and

    Vₖ=pVₖ₋₁−q²Vₖ₋₂  for k≥2.

For every prime ℓ dividing q, induction gives Vₖ≡pᵏ (mod ℓ). Since gcd(p,q)=1, gcd(Vₖ,q)=1. For n≥2 the orbit point is

    Cⁿe₁=(−qVₙ₋₂,Vₙ₋₁)/q^(n−1).

Its bottom numerator is coprime to q, so its joint least common positive denominator is exactly q^(n−1). At n=1 the point is e₂ and its denominator is also q⁰=1. The n=0 point e₁ has denominator 1 as well.

**Important index distinction.** A denominator qᵐ forces the unique possible positive time n=m+1. The time-zero point e₁ must still be excluded separately. Treating denominator 1 as forcing only n=0 or only n=1 would be incorrect.

The proof allows even and composite q, either sign of p, repeated prime factors, and zero coordinate components. It uses no prime factorization algorithm.

## 3. Integer power coefficients and bounded extraction

Let β be a root of

    f(Z)=Z²−pZ+q².

Its conjugate root is distinct; both have modulus q. The discriminant parameter δ=4q²−p² is a positive integer. Write uniquely

    βⁿ=Cₙ+Dₙβ,   Cₙ,Dₙ integers.

These coefficients exist by reduction modulo the monic f. They satisfy

    C₀=1, D₀=0,
    Cₙ₊₁=−q²Dₙ,   Dₙ₊₁=Cₙ+pDₙ.

For n≥1, Dₙ=Vₙ₋₁; for n≥2, Cₙ=−q²Vₙ₋₂. In particular Cₙ is divisible by q for all n≥1, including C₁=0. Consequently

    Cⁿe₁=(Cₙ/q,Dₙ)/q^(n−1)  for n≥1.

Since β−β̄ has magnitude √δ,

    Dₙ=(βⁿ−β̄ⁿ)/(β−β̄),
    |Dₙ|≤2qⁿ/√δ≤2qⁿ.

Also |Cₙ|≤2q^(n+1) for n≥1, by Cₙ=−q²Dₙ₋₁; the n=1 case is zero. For a natural m and P=qᵐ, put

    n=m+1,   H=2q²P,   R=4H+|p|+1.

Then |Cₙ|,|Dₙ|≤H, and R≥2. Here H and R are affine expressions in the POWER output P, not separate witnesses.

The integer polynomial identity Zⁿ−Cₙ−DₙZ is divisible by f(Z), so

    Rⁿ≡Cₙ+RDₙ (mod R²−pR+q²).

Suppose another integer pair C,D has |C|,|D|≤H and the same congruence. Then

    |(C−Cₙ)+R(D−Dₙ)|≤2H(1+R)<R²−pR+q².

For the strict bound, using R=4H+|p|+1,

    R²−pR+q²−2H(1+R)
    ≥R(R−|p|−2H)+q²−2H
    =R(2H+1)+q²−2H>0.

The integer on the left of the first inequality is a multiple of the positive modulus, so it is zero. Since |C−Cₙ|≤2H<R, the equation C−Cₙ=−R(D−Dₙ) then forces D=Dₙ and C=Cₙ. This proves exact bounded coefficient extraction with one ordinary power R^(m+1).

## 4. Explicit outer equations

Choose a positive integer tⱼ clearing the entries of Sⱼ⁻¹, and put the fixed integer matrix Mⱼ=tⱼSⱼ⁻¹. Define the integer linear input expressions

    Uⱼ=Mⱼ₁₁X+Mⱼ₁₂Y,
    Vⱼ=Mⱼ₂₁X+Mⱼ₂₂Y,
    Wⱼ=tⱼN>0.

Thus Sⱼ⁻¹x=(Uⱼ/Wⱼ,Vⱼ/Wⱼ), also at x=0.

For the strict-kernel version choose a fixed positive integer L clearing Q and r², and write a=Lr²>0 and the integer symmetric matrix G=LQ. Define

    Δ=aN²−G₁₁X²−2G₁₂XY−G₂₂Y².

Introduce one shared natural d and the equation Δ=d. This is exactly Δ≥0. For the pure orbit-complement version, omit d and this equation and replace d² by 0 in the two acceptance equations below.

For each contact independently introduce natural

    m,k,L_C,H_C,L_D,H_D;

strictly positive

    h,b,r,s,t,J₀,J₁;

and unrestricted signed integer

    u,v,e₁,e₂,e₃,C,D,κ.

Instantiate the full POWER module in Section 6 twice, using independent internal witnesses:

    P=POWER(q,m),
    H=2q²P,   R=4H+|p|+1,
    T=POWER(R,m+1).

The output leaves P,T belong to their modules and are not counted again. H,R and m+1 are expressions. Add these fourteen residual equations per contact:

1. Uⱼ=hu
2. Vⱼ=hv
3. Wⱼ=hb
4. e₁u+e₂v+e₃b=1
5. b=Pr
6. r=qk+s
7. s+t=q
8. C+H=L_C
9. H−C=H_C
10. D+H=L_D
11. H−D=H_D
12. T−C−RD=κ(R²−pR+q²)
13. d²+(u−b)²+v²=J₀
14. d²+(r−1)²+(qu−C)²+(v−D)²=J₁

All natural variables, including zero-valued slack variables, are represented by z=z₊−1 with z₊>0. Every signed variable is represented by z=z₊−z₋ with z₊,z₋>0. These are affine substitutions and introduce no separate adapter equations. Positive variables remain single positive leaves.

## 5. Soundness and completeness of the outer formula

Equations 1–4 imply gcd(u,v,b)=1 and h=gcd(Uⱼ,Vⱼ,Wⱼ)>0. Conversely these canonical quantities admit signed Bézout coefficients. Therefore b is exactly the joint least common denominator of Sⱼ⁻¹x. Indeed, if a positive integer a clears both coordinates, then b divides both au and av; multiplying the Bézout equality by a proves b divides a. This argument also handles x=0, where u=v=0 and b=1.

The first POWER module gives P=qᵐ. Equations 6–7 say 1≤s≤q−1 and k≥0, hence q does not divide r. Every positive b has a unique factorization

    b=qᵐr,  m≥0, r>0, q does not divide r,

obtained by repeated division by the *whole integer* q. This remains true for composite q; it is not being described as an additive prime-adic valuation. The remainder r may share some prime factors with q.

Equations 8–12, the second POWER module, and Section 3 force

    (C,D)=(Cₘ₊₁,Dₘ₊₁).

The modulus is strictly positive, the true coefficients lie within the inclusive bounds, and the congruence quotient κ is allowed either sign.

The time-zero forbidden equality is exactly (u/b,v/b)=e₁, equivalently u=b and v=0. Thus equation 13 with positive J₀ excludes exactly this point when d=0. If d>0 it excludes nothing.

At any positive time the exact-denominator lemma gives

    Sⱼ⁻¹x=Cⁿe₁ for some n≥1
    iff r=1, qu=Cₘ₊₁, v=Dₘ₊₁.

For the forward implication, b=q^(n−1) forces m=n−1 and r=1. For the reverse implication, r=1 gives b=qᵐ, and the numerator formula in Section 3 proves equality at n=m+1. Consequently equation 14 excludes exactly all positive-time matches when d=0. If d>0 it excludes nothing.

For the kernel, Δ=d with natural d excludes all points outside the closed ellipse. Inside it d>0 makes both positive acceptance witnesses available automatically. On its boundary d=0, all contacts' equations 13–14 are solvable precisely for simultaneous backward-orbit avoidance. This proves soundness.

For completeness choose the positive gcd and primitive quotient, Bézout coefficients, unique whole-q factorization, exact β-power coefficients, their nonnegative bound slacks, the integer extraction quotient, and POWER witnesses. At any accepted input the displayed right sides J₀,J₁ are positive integers. Each natural or signed value admits the stated positive adapter. This constructs witnesses for every accepted input. No disjunctive selector, orbit-search bound, generic MRDP theorem, or rational Euclidean conjugacy is used.

Duplicate contacts and overlaps of backward orbits cause only redundant conjuncts. No orbit-equivalence classification among contacts is required.

## 6. Full fifteen-equation POWER module and dependency

For an integer expression B₀≥2 and a natural exponent expression e, use directly positive leaves

    out,w,M,g,x_p,y_p,u_p,v_p,s_p,t_p,q_b,q_v,J_p;

two positive leaves α₊,β₊, defining α=α₊+1 and β=β₊+1; and eleven natural variables

    d_wb,d_wk,d_yk,α₁,α₂,σ₁,σ₂,τ₁,τ₂,r₁,r₂.

The natural variables each use one shifted positive leaf. Thus this module has exactly 26 positive leaves including its output. Define k₀=e+1 and m₀=B₀·out as expressions. Its fifteen equations are:

1. x_p²=1+(α²−1)y_p²
2. u_p²=1+(α²−1)v_p²
3. s_p²=1+(β²−1)t_p²
4. β=1+4y_pq_b
5. β+u_pα₁=α+u_pα₂
6. v_p=y_p²q_v
7. s_p+u_pσ₁=x_p+u_pσ₂
8. t_p+4y_pτ₁=k₀+4y_pτ₂
9. y_p=k₀+d_yk
10. w=B₀+d_wb
11. w=k₀+d_wk
12. M=m₀+J_p
13. α²=1+((w+1)²−1)(wg)²
14. 2αB₀=M+(B₀²+1)
15. x_p+Mr₁=y_p(α−B₀)+m₀+Mr₂

This is the explicit Report 59 module. Its mathematical dependencies are `Pell.matiyasevic` and `Pell.eq_pow_of_pell` in mathlib4 commit ac77769fabe23cb237559e7f56578dbead91499f, file Mathlib/NumberTheory/PellMatiyasevic.lean, SHA-256 993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a. The relevant source statements are at lines 760–766 and 860–864 of the inspected inert source. This is a theorem specialization, not a claimed new proof or local Lean build.

Every truncated natural subtraction in the source Pell identities has been translated exactly. For natural a,b, the identity a−b=1 (natural subtraction) is equivalent to a=b+1. Since α,β≥2 and w≥2, the inner subtractions α²−1, β²−1 and (w+1)²−1 are ordinary nonnegative differences as well. Thus equations 1–3 and 13 are equivalent to the source Pell identities, not a strengthening of them.

Equations 1–9 are the positive-index Matiyasevic branch, with k₀≥1 and y_p≥k₀. They characterize the Pell pair of index k₀ for α. Equations 10–15 are the positive-base power characterization, with the strict modulus condition M>m₀. Equation 13, w≥B₀≥2 and g>0 imply α>w≥B₀, so the ordinary subtraction α−B₀ agrees with the natural subtraction used by the source theorem. It follows that B₀^k₀=m₀=B₀·out, hence out=B₀^e.

Conversely the constructive source theorems provide the required values. Their auxiliary g is nonzero because α>1; x_p,u_p,s_p and y_p,v_p are positive; q_v is positive because v_p>0. Since β>1 and β≡1 modulo 4y_p, q_b is positive. The congruence t_p≡k₀ modulo 4y_p, with 1≤k₀≤y_p<4y_p, excludes t_p=0. Each congruence quotient can be represented as a difference of two naturals. The strict modulus bound gives J_p>0. The shift k₀=e+1 therefore correctly includes e=0 without zero-valued positive leaves.

Here the first base is q≥2 and the second base is R=8q²P+|p|+1≥2 before invoking either module's semantic conclusion. The second exponent e=m+1 is natural. No input-dependent-base hypothesis is omitted.

## 7. Exact witness, equation, and degree ledger

Per contact the outer variables contribute:

- 6 natural variables, giving 6 positive leaves
- 7 positive variables, giving 7 positive leaves
- 8 signed variables, giving 16 positive leaves
- Two POWER modules, giving 52 positive leaves

Total: 81 positive witnesses per contact. There are 14 outer equations plus 30 POWER equations, total 44 per contact. The kernel adds one natural radius witness and one equation. Thus:

    Orbit complement: 81J witnesses, 44J equations
    Strict kernel:     1+81J witnesses, 1+44J equations

Inputs are not witnesses. A physical specialization to three positive input gaps does not add witnesses when X,Y,N are fixed linear expressions in those gaps. If a one-positive-input transport is desired for such a three-gap specialization, the same paid Cantor decoder as Report 59 adds four positive witnesses and two quadratic equations, giving 5+81J witnesses and 3+44J equations for the kernel. That transported formula has a different input ledger.

Define F literally as the sum of squares of all displayed residual polynomials after substituting every input alias, H,R,k₀,m₀, Pell-parameter shift, natural shift, and signed difference. Fixed rational coefficients have already been cleared in U,V,W and Δ, so F has integer coefficients. Because all variables range over ordinary positive integers, F=0 is equivalent to simultaneous satisfaction of all equations.

Every outer residual has total degree at most three: the only cubic type is κR². Every POWER residual has total degree at most six, even in the module whose base R is affine in the other module's independent output P. Equation 13 of each module has leading monomial −w⁴g² of degree six. Its square contributes w⁸g⁴. A nonempty sum of squares of nonzero real leading homogeneous polynomials cannot cancel identically. As J≥1, F therefore has exact degree 12.

This is a literal finite polynomial schema with explicit adapters, not a named exponentiation oracle. No exact arithmetic gate count, optimized DAG, unique witness, finite-fold representation, small-height witness bound, or efficient construction of the Pell witnesses is asserted.

## 8. Elementary rational decision algorithm and uniform scope

For any rational infinite-order elliptic A and nonzero rational contact z, compute S⁻¹x and its primitive joint denominator b. First test equality with e₁. Otherwise repeatedly divide b by q while divisible, obtaining b=qᵐr. If r≠1, no positive-time match exists. If r=1, compute the recurrence coefficients at n=m+1 and compare the integer pair (qu,v) with (Cₙ,Dₙ).

There are at most log₂b divisions and recurrence steps, and the coefficients at the relevant exponent have bit length O(log b+log q). The bounds in Section 3 apply to every intermediate exponent as well. Standard exact rational matrix operations in dimension two have polynomial bit complexity. Consequently the point-to-point backward-orbit test here is polynomial-time uniformly in A,z,x. No prime factoring and no general Orbit Problem subroutine are needed.

Combining these tests with the rational Q, r² and contact construction gives a uniform polynomial-time decision algorithm for the elliptic strict-kernel branch when A, the rational polygon and x are all inputs. This algorithm does not calculate R^(m+1), much less Pell witnesses; those powers are used only in the existential polynomial proof. No uniform polynomial-time result for unrelated stable-matrix branches follows from this argument.

## 9. Fresh exact checks and limitations

The accompanying newly written `check_certificate.py` uses standard-library integer and rational arithmetic to test the denominator, coefficient, radix-margin, extraction-congruence and direction claims for signed traces, even and composite trace denominators, zero and positive times, rational basis changes, primitive input reductions, and strict acceptance. All checks passed: 1,292 reduced signed traces with 2≤q≤32, 32,300 orbit powers, 330,752 whole-base factorizations, 255 rational-conjugacy instances, 7,752 additional rational-point tests, 325 strict-radius/gate cases, and four exhaustive small bounded-extraction searches. It also contains a fresh sparse-polynomial implementation of the complete positive-adapted one-contact kernel schema, checking 82 positive witnesses, 45 equations and degree 12. Only this inspected new code is executed.

Finite fixture checks support the proof but do not establish its all-input quantifiers. The all-exponent POWER equivalence remains the explicitly identified constructive Pell theorem dependency. No legacy constructor, legacy checker, upstream Lean program, physical simulator, or event-driven trajectory is executed by this artifact.

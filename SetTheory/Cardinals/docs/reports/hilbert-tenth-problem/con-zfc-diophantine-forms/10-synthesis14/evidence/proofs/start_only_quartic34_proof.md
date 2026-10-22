# Explicit quartic alternative: 34 positive variables, 25 quadratic equations

This is the final low-degree alternative for this round. Its constants are exactly the four fixed constants of the Start-only 67-operation polynomial. It is not an optimization or a new claim about the 67-operation count.

## Fixed constants and unknowns

The fixed positive integer numerals are β=`Bm1`=B−1, K₀=`Kconstant`, M_C=`MC`, and M_F=`MF`. The last port uses the inherited shifted verification-mask convention, not the unshifted native mask. Their fixed finite compiler recipe is supplied by the main construction. None is quantified.

The 34 unknowns are all strictly positive integers:

    J,F,α,z,f,h,i,T,s,w,τ,η,ζ,y,γ,
    N,E,P,c,a,X,D,C₂,K,G,L,R,F₂,V₀,V,g,I,B_aux,Δ.

The first line lists the 15 original unknowns. The second line contains 19 added register unknowns. Define only the following affine abbreviations:

    q=βJ+1,       k=η+ζ,       H=4a+3,       C=q−F−α.

These abbreviations are not additional variables or extra equations. Since they are affine, expanding them preserves the quadratic degree bounds below.

## The 25 literal equations

1.  L = q²−1.
2.  N = q(L+1).
3.  X = wq.
4.  a = E+sN.
5.  E = X(a−E).
6.  c = k(a−E)+η.
7.  P = E(c−η)+k.
8.  τ² = P(P−k)+1.
9.  D = X+ac+γH.
10. K = D²−1.
11. Δ = a²+H.
12. C₂ = c².
13. K = ΔC₂.
14. k = R+1+hE.
15. G = (q−1)(q−F)+α.
16. R = LG+(M_C+qM_F)J.
17. (K₀+w)C+(q−F)−z(q−1) = 1.
18. F₂ = f².
19. V₀ = Tf−1.
20. V = cV₀−RF₂.
21. g = y²−V².
22. I = iK.
23. B_aux = I².
24. B_aux = Δ(F₂−1).
25. y²−B_aux g = 1.

Every side is an ordinary polynomial of total degree at most two in the 34 unknowns, after expanding the four affine abbreviations. Fixed compiler constants have degree zero. The complete expanded integer-coefficient residuals are provided, not merely a generator, in `start_only_quartic34.json`.

## Single polynomial over the nonnegative integers

Let r_j be left side minus right side in equation j. For v=(v₁,...,v₃₄), put

    Q(v)=r₁(v)²+...+r₂₅(v)².

This is one ordinary quartic polynomial. For nonnegative witnesses n₁,...,n₃₄, use the single equation

    Q(n₁+1,...,n₃₄+1)=0.

The finite 25-term sum is literal: there is no variable-length conjunction, bounded universal quantifier, exponentiation relation, or computation predicate left in it. Its exact degree is four. For example r₁ contains −β²J², with β>0; thus some residual has a nonzero quadratic leading form, and the sum of squares of the quadratic leading forms cannot vanish identically over the reals. The shift n↦n+1 preserves degree.

## Algebraic equivalence with the six-equation Start-only system

Equations 1-4 give N=q³, X=wq and Y:=a−E=sq³>0. Equation 5 gives E=XY, hence a=Y(X+1). With k=η+ζ, equation 6 gives c=kY+η. Equation 7 gives P=EkY+k. Therefore equation 8 is exactly the original first Pell-norm equation

    τ²−(EkY)(EkY+k)=1.

Equations 9-13 give

    D=X+ac+γ(4a+3), Δ=a²+4a+3, D²−Δc²=1.

Equations 14-17 give the original positive index and transport equations. Indeed G=q(q−F)−C=q²−C−qF, so

    R=(q²−C−qF)(q²−1)+(M_C+qM_F)J.

Equations 18-24 give

    V=c(Tf−1)−Rf²,
    B_aux=(iΔc²)²=Δ(f²−1).

Since Δ>0, the latter is exactly the scaled-strong equation of the 61-operation system. Equations 21 and 25 give

    B_aux(V²−y²)+y²=1,

the original auxiliary equation. Thus every positive solution of the 25 equations yields a positive solution of the source's six equations at the same 15 original unknowns.

Conversely, each positive solution of the six-equation source has a unique assignment of these 19 register values. All are strictly positive. Most are immediate sums/products of positive values. For the less immediate ones:

* q>1, so L=q²−1>0.
* The source transport equation gives C>0: if C≤0, its non-C part is 1−F−(z−1)(q−1)≤0, so it cannot total 1. Thus q−F=C+α>0 and G=(q−1)(q−F)+α>0.
* The native packing bounds give R>0, already established in the source theorem.
* The normalized-strong equation gives f>2c>0, so V₀=Tf−1>0.
* The source auxiliary restoration proof gives V>1 and B_aux>1. Its auxiliary equation implies (B_aux−1)(y²−V²)=V²−1>0. Hence g=y²−V²>0.
* I=iΔc²>0 and B_aux=I²>0.

No inequality has been silently added to the final polynomial: positivity is the declared domain, or is enforced by the explicit nonnegative shifts. The proof above shows the introduced positive coordinates do not remove any original solution.

Consequently, once the main Start-only compiler theorem is instantiated at the fixed ZFC recognizer, ZFC proves

    Q(n₁+1,...,n₃₄+1) has no solution in N³⁴  iff  Con(ZFC).

This is an additional degree/variable tradeoff, not a claim that 34 variables or degree four is globally minimal for this particular undecidable statement.

## Independent audit trail and freeze

The first reduction, from the 61-gate/six-comparison source to 35 variables and 26 quadratic equations, was independently checked using a separately authored sparse-integer-polynomial verifier, not the SymPy reducer. It verified all 41 elimination steps, degree preservation, and the exact final polynomial multiset. Its receipt is `diophantine_zfc_review/quadratic_reduction_independent_audit.json`.

The final 35-to-34 conversion replaces two registers U=ac and Gₘ=γH with one register X=wq and renames B_aux=S−Δ=I². The positive inverse is U=ac, Gₘ=γH, S=B_aux+Δ. In the explicit residual ordering, old residual 3 equals new residual 3 plus new residual 9; old residual 5 equals new residual 5 minus (a−E) times new residual 9. Two old residuals become zero, and every other old residual agrees with a new residual up to sign. `build_quartic34.py` checks all these identities exactly. The final independent sparse-polynomial audit also passed: it checked all 26 old residual identities, every factored equation against its printed expansion, the positive projection and lift, and exact quartic degree (the coefficient of τ⁴ is 1). Its receipt is `diophantine_zfc_review/quartic34_independent_audit.json`. The final JSON SHA-256 is `84bac06eb0366d57ebdfd887b61927a8468bba8b5ca0066996cbc6096ac1b524`. Counts are frozen at 34 positive variables, 25 quadratic equations, one quartic sum of squares.

# Independent review: eleven-integer two-group projection

## Verdict and scope

PASS. The new pair has the asserted mathematical zero-existence equivalence, relative to the explicitly retained ordinary native/compiler/refutation calibration. I found no new proof gap in the two-group construction, rational clearing, coprimality extraction, signed soundness transport, or fixed-strong-pair completeness. The five nondominated integer endpoints in this package are exactly

- degree 688, 124 binary operations;
- degree 728, 120 binary operations;
- degree 820, 119 binary operations;
- degree 964, 118 binary operations;
- degree 1632, 112 binary operations.

The middle two are new mathematical reductions; the other three are evaluator optimizations of the retained predecessor. All eight supplied circuits, including three dominated comparisons, were independently audited. The eight results appear in `INDEPENDENT_CHECK.json` and `INDEPENDENT_CHECK_OPTIMIZED.json`.

This is an ordinary proof review and exact finite computational audit, not a Lean/Rocq proof, a new internal object-ZFC derivation, a proof of Con(ZFC), or a minimality claim. The source calibration is retained as an ordinary dependency; authenticating its bytes does not formally certify its unbounded assertions.

The reviewer read `integer/PROOF.md` in full, the full retained centered eleven-integer and signed-quadratic proofs, the predecessor integer proof, and the intersectivity proof. Particular attention was given to the three changes identified below. The independent program imports no producer builder, checker, or polynomial-ring implementation. It never modifies producer files.

## 1. Nonzero bootstrap and rational clearing

The affine restrictions give even nonzero q, X divisible by 8, nonzero Y, |a| sufficiently large, A and H nonzero, H odd, and Delta=A^2-1>1. The integer consecutive-product identity gives Dt>=1; Dm,Df>=1. These facts hold before a zero is assumed and do not require oriented signs.

If I=0, then S=Q=0 and delta=-1. Both new polynomial outputs are exactly Ac^4. Since Ac=H^5 pi(T+K/H), H is nonzero and pi(t)=(t^2+3)(t^3-19) has no rational root, this branch has no zero. Thus I,s,r,c are all nonzero at a zero. The new multiplier is divisible by c^2, so |I|>=c^2. It follows that Q>1, delta>0, Df>|c|+1, V!=0, and Cy,Da>0. This justifies dividing by S or delta only in the proof, never in the literal DAG.

For the integral polynomial, the four-factor identity has radicands Df*Da and P. For the rational polynomial, the formal product uses Df*Cy/delta and P, multiplied by delta^2. The independent exact expansion checks the stated denominator-cleared arrangement and the rearrangement obtained by clearing the other quadratic norm first. No spurious delta=0 branch exists: Q=(Delta I)^2 cannot be 1, and at a zero Q>1.

If Dg<0, then P<0, whereas the other radicand is positive. In a vanishing conjugate the P term is the only nonzero imaginary term, an impossibility. Since Dg is odd, it is positive. If Budget<=1, then D<=-1 and s!=0, Dt>=1 imply Dg<=-3. Therefore Budget>=2. The centered disk/sign implications then apply before any main-root or orientation argument.

## 2. Rational parity extraction is valid

The integral factor, divided by nonzero S, is a rational signed sum of sqrt(Df*Da) and 2 sqrt(P). In the rational case, multiply the divided factor by the positive odd integer delta. It becomes a rational signed sum of sqrt(Df*Da) and 2 delta sqrt(P). This multiplication is essential: it converts the nonintegral-looking radicand into the same positive odd integer Df*Da.

Because I is even, Df and Da are 1 modulo 4; Dt,Dg,P and delta are odd. Every positive odd integer radical is an odd integer times the radical of an odd squarefree integer. If both terms belonged to the same nontrivial squareclass, their rational coefficients would have 2-adic valuations 0 and 1, respectively, in either polynomial. They cannot cancel. If they belong to distinct nontrivial classes, squarefree-radical linear independence excludes the rational sum. A lone irrational class likewise cannot survive. Thus Df*Da and P are both integer squares.

This reasoning does not assume the two groups are coprime, and it does not infer that arbitrary radicals in a rational sum are separately rational. The unequal valuations supply exactly the missing noncancellation hypothesis.

## 3. Both within-group coprimality arguments are valid

The guard identity immediately gives gcd(Dt,Dg)=1.

For the strong/auxiliary group, modulo Df=1+Delta I^2,

    Q = -Delta, delta = -A^2, V = -c, Cy = -Dm,
    Da = A^2 Dm.

The congruence has also been checked as an exact integer-polynomial identity, not merely by samples or by division over a rational function field. With b=c-R+4IT,

    Da-A^2 Dm
      = Df*Delta*[Cy-A^2*(V^2+b*(c-V))].

Since A*Dm divides I, Df is 1 modulo every prime divisor of A or Dm. Hence gcd(Df,A^2 Dm)=1 and therefore gcd(Df,Da)=1. All four radicands are positive. Coprime product-square extraction now proves that Df,Da,Dt,Dg are separately squares.

The added factors are doing real work. As arithmetic controls (not authentic outer witnesses), omitting A can give A=10,c=2,I=3176 and gcd(Df,A^2 Dm)=25; omitting Dm can give A=2,c=5,I=100 and gcd=19. These examples illustrate why the supplied coprimality proof cannot simply drop those factors.

## 4. The adjacent Pell descent and scalar projection

Let ytilde^2=Da and y=ytilde/delta. Then QV^2-(Q-1)y^2=1. The retained denominator descent is valid under exactly the supplied Q>1 and integer V hypotheses. If y=a/b is reduced, b^2 divides Q-1. Consequently

    V'=(2Q-1)V-2(Q-1)y,
    y'=(2Q-1)y-2QV

preserve the equation and make V' integral. Modulo b, the numerator of y' is congruent to a, so the reduced denominator stays b. After independently choosing positive signs, V>1 implies 0<V'<V: use V<y<sqrt(Q/(Q-1))*V. The process terminates at V=1, where y=1. Thus b=1. This rules out a rational-but-nonintegral auxiliary ordinate.

The factor equation is consequently integral after division by S, with terms f*delta*y and 2*tau*g in the integral form, or f*y and 2*tau*g in the rational form. Hence S divides Ac.

The prime-adic monicity argument for H^5|Ac implies H|K and works for either sign of H. If v_p(HT+K)=b<e=v_p(H), the leading fifth power has valuation 5b, while each other homogeneous term has strictly greater valuation. This contradicts p^(5e)|Ac. The exact identity K=HXc-2Kquad and odd H then give H|Kquad without cancellation of a nonunit.

## 5. Signed soundness does not use an illicit odd multiplier

The change to I=2src^2 A Dm preserves every input used by the inherited pre-projection rank argument: nonzero I; c^2|I; the positive strong, first and auxiliary norms; the centered |c|/|k| strip; common-sign packing; and the residues V=-c modulo f and V=-R modulo c. The second residue follows directly from

    V+R=Delta I^2(c-R)+4I Df T.

No property in that prefix requires I/c^2 to be odd. The strengthened divisibility only helps.

The omitted main Pell classification is recovered before orientation. For B0=|A|, |I|=psi_B0(m0) and |f|=chi_B0(m0)>2|I|. The auxiliary odd-index quotient supplies psi_B0(nu)=+/-|c| modulo |f|. Folding nu modulo 2m0 and reflecting gives 0<=p<=m0. Since psi_B0(p)+|c|<=2|I|<|f|, no wrap is possible; |c|=psi_B0(p), p>=1. This does not need the main congruence or a sign assumption.

The retained nonodd strong-rank argument is justified by Lucas composition: strong divisibility first gives p|m0; writing m0=pv and chi_B0(p)=D0, the congruence psi_D0(v)=v D0^(v-1) modulo |c| and gcd(D0,|c|)=1 give |c||v. In particular m0>2p. The signed auxiliary step-down then yields p=R, and the first norm gives R=2t+1 and the required uniform growth bound.

The whole-product projection uses H|Kquad and an absolute bound, not cancellation modulo composite H. It forces sign(c)X=2^R. Only then are centered orientation and half-binomial recovery used to obtain X,c,k,Y>0 and 0<eta/k<1/4. Fresh odd strong/auxiliary witnesses are regenerated after that recovery. The incoming even multiplier is never relabeled as odd. The restored old signed witness is the point where the retained compiler/refutation calibration is invoked.

## 6. Fixed-strong-pair completeness, including the inherited theorem

Completeness has the correct quantifier order. Canonical outer data fix A,Dm,Dt,Budget and the projection. Since Dt=1 modulo 3 and D=3Budget-4, the positive integer D*Dt is 2 modulo 3 and is nonsquare. Pell existence therefore supplies s,g>0 with g^2=1+4D Dt s^2. This guard choice is independent of I and T.

Now N=2s A Dm is a fixed positive integer. The retained full-residue theorem produces one positive strong pair I,f with 4N c^2|I, equivalently 8s A Dm c^2|I, before any residue is requested. The choice r=I/(2s A Dm c^2) is therefore integral and realizes the new multiplier exactly. Increasing N does not change the theorem's quantifier structure.

The full proof of that theorem was inspected. Its relevant points are:

1. The determinant-one Pell matrix has finite order modulo 4N c^2, so one may choose an even positive strong index n0 with the required divisibility.
2. For each prime p|I=psi_A(n0), v_p(I)>=v_p(n0). The odd-prime rank/lifting argument and the even-A doubling formula at 2 establish this.
3. If alpha=A+sqrt(A^2-1), the identity alpha^(4n0)=1-4f alpha^n0 modulo f^2 gives alpha^(4n0 f)=1 modulo f^2. The extra factor f is indispensable.
4. With lambda=4n0 f, gcd(lambda,4I^2) divides 4I. Hence, for every residue a, the system L=R modulo lambda and L=R-4Ia modulo 4I^2 is compatible.
5. Canonical R=3 modulo 4 and c=R modulo 4 supply the signs and factor 4 in the odd quotient identity. The resulting V0 satisfies V0=-c modulo f^2 and V0=-L modulo 4I^2.
6. The numerator V0+c-f^2(c-R) is divisible by 4I f^2; after division, T=a modulo I, since f^2=1 modulo I. Thus every a is realized by the same I,f.

The independent controls construct three fixed strong pairs for A=2,R=3,c=15 and N=1,2,3, of 170,341,512 bits respectively. For each fixed pair they check five requested residue classes through exact modular Pell exponentiation and the CRT numerator. They also reject 4n0 as a substitute for the correct period 4n0 f. These are finite controls, not substitutes for the preceding unbounded proof.

Only after I,f,r are fixed does intersectivity choose a root of pi(T+kappa) modulo I, where kappa=K/H. The already fixed pair realizes that class. Hence Ac/S=pi(T+kappa)/I is integral, and the specified n makes the relevant conjugate vanish. There is no reselection of I after choosing a residue and no cycle between the guard and strong witnesses.

The retained intersectivity proof handles ordinary primes by the cubic discriminant, p=19 by the simple quadratic root 4, p=2 by the simple cubic root 1, and p=3 via x=1+3t and the simple equation t+3t^2+3t^3=2. CRT applies. The nonvanishing and intersectivity roles of the quintic are separate and both are supported.

## 7. Literal formulas, gates, and numeral binding

`check_independent.py` checks that all nodes are integer/coordinate/fixed-numeral leaves or binary addition, subtraction and multiplication; that every edge points backwards; that precisely the stated eleven coordinates and six fixed numeral leaves occur; that every node is live; and that the arithmetic counts match an independently fixed expectation. Every live arithmetic node is covered by exact SymPy polynomial identities against a separately transcribed mathematical register specification.

The four-factor and eight-factor products are multiplied directly in independent symbolic variables. Their equality with both new norms and the balanced older octic is exact. The program also checks the scalar-projector identity, strong/auxiliary congruence, rational clearing, and the centered cancellation identities. Malformed-gate, dead-node and false-count mutations are all rejected under normal Python and under Python -O.

All six actual compressed numeral payloads are decompressed and authenticated by their raw hashes, byte counts and bit lengths. They are then independently reconstructed from the retained literal 943-tile list and 989-position packing formulas without importing the producer's recipe. This includes the shifted MF convention. The entire current set of 95 pinned source/license dependencies is authenticated. The retained predecessor proof was additionally compared byte-for-byte with the previous package and is unchanged.

## 8. Exact degree upper bounds and independent lower witnesses

For the new pair, the prefix degree bounds are I=24, S=54, Df=60, Q=72, V=85, Cy=242, Da=314, P=94, Ac=35 and Z=55. In the integral form, S^2 Df Da has degree bound 482, versus Z^2 at 110 and 4S^2P at 202; the final other product is at most 684. Thus the total degree is at most 964. In the rational form, S^2 Df Cy has degree bound 410, versus delta Z^2 at 182 and 4delta S^2P at 274; the final other product is at most 456. Its total degree is at most 820.

The direct optimized octic has u,b,e bounded by 88,182,162 and Z by 35, giving degree at most 728. For its auxiliary-centered sibling, B=Sn-Ac has degree at most 35 and C0=S(2Q-1)V has degree 91. The exact identity b-C0^2=S^2(-V^2-4Q+4) gives omega=Z^2-b degree at most 126. Rewriting the balanced inner expression as (omega-u-e)^2-4(ue+b(u+e)) bounds it by 344. Its square has bound 688 and the remaining product has bound 614.

For the optional diagnostic centers, write Z=B+S lambda V. Then

    rnorm=S^2[Q(lambda^2-Df)-lambda^2]V^2+S^2 Df
           +2delta S lambda V B+delta B^2+4delta S^2P.

For lambda=AI, lambda^2-Df=I^2-1. For lambda=(2Delta+1)Ib, lambda^2-Df=Ib^2-1. The resulting rnorm bounds are 398 and 386, giving degrees at most 796 and 772. Both shifts are integer polynomials independent of n, so their zero-existence equivalence follows by a bijective change in n. They are dominated and are not new frontier points.

The all-fused inherited rational and integral endpoints have the unchanged degree upper bounds 1632 and 1892. The independent program propagates literal degree bounds with only the exact cancellation cuts described above.

For a genuinely independent lower-bound method, the program evaluates each entire literal DAG in the exact univariate ring F_65521[t], mapping its eleven coordinates to t,2t,...,11t and reducing the actual authenticated huge numeral coefficients modulo 65521. The resulting degrees are exactly the eight claimed degrees, with nonzero top coefficients. This is a rigorous lower-degree certificate: a specialization and coefficient reduction cannot increase degree. Combined with the independent upper bounds, it proves the original fixed-numeral polynomial's exact total degree. It is not a random numerical estimate and does not rely on the producer's leading-monomial implementation.

## Reproduction

From the package root:

    python review/integer/check_independent.py
    python -O review/integer/check_independent.py

Dependency: SymPy (tested with version 1.14.0). Paths are derived from the script location, so the package may be relocated. The two JSON reports are identical apart from their filenames. No assertion statement is used for a substantive test. The script only writes its own two review outputs.

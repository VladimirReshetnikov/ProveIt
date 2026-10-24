# Independent arithmetic review of the two new direct quartics

Date: 24 October 2026. This is an independent review within the same AI-assisted research session, not external peer review or a proof-assistant certificate.

## Reviewed objects and verdict

I reviewed the ordinary proofs and their literal interfaces in:

- `alternative_route/MODULAR_NUMERATORS_PROOF.md`, `alternative_route/modular_factorial.py`, and the generated `dominant12_cantor` packet;
- `frontier_audit/PARITY_PROOF.md`, `frontier_audit/even_architecture.py`, and the generated `even_modular12` packet;
- the frozen Round14 factorial-carrier, reciprocal-CRT, and derived-label-range proofs on which both constructions depend;
- the previously delivered even-index proof and its signed-index theorem.

**Verdict:** the two new arithmetic reductions are sound and complete under the explicitly inherited C222/source and Pell interfaces. I found no remaining mathematical blocker. They produce ordinary proofs formalizable in ZFC, not new kernel-checked proofs. The proof-calculus/refutation calibration remains an inherited dependency and was not independently re-formalized here.

The 332-natural-variable construction preserves the old semantic source and changes the private power implementation. The 333-natural-variable construction additionally changes parity, strict bounds, and the index certificates. These are existential equivalences with newly chosen private Pell witnesses; they are not pointwise identifications of old and new witness vectors.

## 1. The dominant modulus is justified before factorial interpretation

For the 332-variable construction, let the proposed factorial output be F and write the two raw ceiling rows as

    V+c=cF+r+1,       c=r+s+1.

Exact recovery of the retained power gives V=(Ft²+1)^t>0. Eliminating c gives cF=V+s>0, hence F>=1. This reasoning does not assume that c is a binomial or that F=t!.

The raw endpoints then imply y>=2 and x>=2. Consequently the last endpoint

    x=1+[1+(t+1)y]u_t

forces u_t>=1 and x>=2+(t+1)y. In particular x>t+1 and x>y+1. Therefore M=Nq^(x+1) is a multiple of q^(t+1) and every required Nq^k. No exact digit is used to justify its own modulus.

In the 333-variable construction, x=2x0+2 and y=F+2r0+2 already give x,y>=2. The same last endpoint yields x>2t,y,t before any power or factorial interpretation. Thus its smaller existing modulus M=Nq^x covers q^(t+1) and all Nq^k for k in {t,x,y,2t}.

## 2. Cofinal Pell parameters and the root congruence

The modified scale has L²-W³(W+2)Z²=1, Z>=1, and A=L+s with s>=0. Classification at base W+1 and reduction of the ordinate modulo W imply a positive index divisible by W. Hence L>W^W and A>=L. Conversely the actual Pell solution at index W supplies an allowed L,Z; then every sufficiently large A is allowed.

This cofinality is important. It lets the common modular root condition

    2A(q+1)=(q+1)²+1+Mh

be solved after the semantic values, q, M, and W have been fixed. Since N divides q, gcd(q+1,M)=1. For the 332-variable version, gcd(2(q+1),M) is either 1 or 2. In the latter case q is even, q+1 is odd, and the right side is even, so the congruence is soluble. In the parity version, true F=t! makes B,N,V,N+V+1,q and M odd, so the coefficient is directly invertible modulo M.

An arbitrarily large member of the resulting residue class gives A>=L and A>q+1, and the root quotient h is nonnegative. The private frame must be rebuilt at this chosen A. Retaining the parent's particular A would not prove completeness.

## 3. Modular numerators and natural quotient witnesses

In the Pell ring, substituting the quadratic generator by q+1-A is valid modulo M precisely because of the root congruence. Therefore

    chi_A(n)+(q+1-A)psi_A(n) = (q+1)^n mod M.

The exact digit modulus is q^(k+1); a divisibility digit needs Nq^k. Each divides M by the endpoint lemma. Uniqueness of residues in [0,q^(k+1)) recovers the exact binomial digit; residues in [0,q^k) modulo Nq^k express divisibility of that digit by N.

The natural domain is respected in both directions. For n>=1, the Pell norm gives chi_A(n)>(A-1)psi_A(n), so the modular representative is positive. A positive representative congruent to the least nonnegative residue has a nonnegative quotient. Alternatively, after choosing A>q+1, the exact polynomial identity

    chi_A(n)+(b-A)psi_A(n)-b^n
      =(2Ab-b²-1) sum_{j=0}^{n-1} b^(n-1-j)psi_A(j)

with b=q+1 shows directly that the new representative exceeds the original numerator by a nonnegative multiple of M.

There is no justification here for dropping the natural signs of the modular-only Pell pairs. The delivered polynomials keep the nonnegative domain.

## 4. The factorial bootstrap and horizon twelve

I checked the dependency order of the carry estimates. The retained exact powers are interpreted before any binomial. From V>0 the ceiling rows give F>=1 (and F>=2 in the even version). The raw reciprocal index row gives B>=1. Consequently N>=1 and q=N(N+V+1)^K>V².

For the first exact binomial, rho=Ft²>=t. All coefficients through degree t of (1+z)^(rho+t) are bounded by binom(rho+t,t)<=(rho+1)^t=V, independently of the proposed output. Thus its digit can be interpreted without circularity. The self-bounding factorial lemma then identifies F=t!, after which the second exact binomial identifies B and the reciprocal-modulus bounds apply.

The numerical base inequalities at t=12 are correct:

    12!=479001600>2^28,
    28*8388608<2^28,
    2*8388608<=2^28,
    12*(3*4194304+1)<=12!.

For r>=2^28, the finite-geometric-series bound on (1+1/r)^E is strictly below 2. This propagates r^E<2^r by induction. The factorial inequality t(3ell+1)<=t! also propagates immediately. These establish the local evaluation bound and the derived-label digit bound at every padded horizon, not just at the checked base value.

## 5. Even index certificates

The 333-variable construction removes the Y>=e slack because every tested seed exponent is already even and positive. This parity is a literal identity using F=2f, not a consequence of F=t!.

The common ordinate V_aux=v0+1 is strictly positive and is a positive multiple of the product of all seed Y². Therefore every seed Y is nonzero. If Y=1, its Pell abscissa is X=A. The abscissa comparison congruence and the standard Chebyshev residue lemma force the comparison index to be odd. The comparison base is odd, so its ordinate is odd; the imposed residue modulo 4Y is even. This contradiction excludes Y=1.

Hence Y>=psi_A(2)=2A. The frame contains every tested seed exponent, so A>W>e and Y>e. The retained standard index theorem is now applicable. The proof of exact index recovery still uses Y²|V_aux to deduce Y divides the common Pell index; merely using Y|V_aux would not suffice.

For completeness, select the actual seed pairs, then choose a common Pell unit congruent to 1 modulo 4 times the product of seed Y². This gives U odd, V_aux positive and divisible by that product, and gcd(U,4V_aux)=1. CRT supplies a comparison base B_aux>=A with B_aux=A modulo U and B_aux=1 modulo 4V_aux. At each seed's actual exponent, its comparison pair satisfies both required congruences and gives nonnegative progression quotients. Thus the deleted index-gap coordinates are unnecessary on the new source family.

## 6. Even representatives and the doubled derived range

The parity restriction on CRT representatives does not change their prescribed residues because the full precision-2K CRT modulus N² is odd. Every residue class has a positive even representative at most 2N². Choosing nine such representatives gives the literal aggregate bound 18N².

In soundness, however, the aggregate row yields only an individual upper bound of 18N², not 2N². The proof correctly uses 18N² for its carry estimates. Once B is decoded, N is enormous; N>=19 gives 18N²+1<=N³. Thus the derived polynomial J satisfies J(A)<=N^(3ell), and its doubled argument satisfies 2J(A)<=N^(3ell+1). The bound 2t(3ell+1)<=2F<K keeps every digit used by binom(2J(A),2t) below q.

The one-sided prime-power range lemma is applied in its valid direction. It supplies a residue r<2t for 2J(A). Polynomial congruence supplies the same residue for 2J(w); the evaluation majorant makes 2J(w)<p^e. Hence equality holds and J(w)<t. No converse of the range lemma is used, and no division by 2 modulo a nonunit is required.

Completeness retains precision 2K. Dividing the falling factorial by k! loses at most k-1<K in p-adic valuation, also for k=2t. This is enough to leave the required K*v_p(d_i) divisibility. The local strict bounds are attainable by padding the horizon first, then choosing even y above every accumulator, and choosing even x by adding the odd product of beta moduli.

## 7. Independent literal checks performed in this review

I compared the first 441 semantic-prefix rows of `dominant12_cantor` against the frozen Round14 `derived16_cantor` raw packet. Exactly one constant differs: the horizon floor 16 becomes 12. The retained wire-source SHA-256 is identical:

    1e7cf2f3ea9397e138c7543d47ccd00a967b8fbb2fd4c8d58f176c409033c1bb

I also wrote `audit_parity_interface.py`, which imports no producer or upstream checker. It reads the 333-variable construction's raw quadratic rows, reconstructs gate right sides, propagates parity over F2, proves conservative unconditional lower bounds, and expands the literal terminal frame sum. It verifies:

- all sixteen seed exponents are even and at least two;
- all sixteen are present among the twenty-six actual frame atoms;
- the frame is exactly two plus the sum of the required distinct exact-power and modular-index atoms;
- the common auxiliary ordinate has the literal form v0+1.

Its receipt is `PARITY_INTERFACE_CHECK.json`. These checks address the principal interface risk introduced by removing the index-gap witnesses. The independent complete polynomial/contraction audits supplied by the other investigators have their own scopes and receipts; I do not relabel those checks as newly performed in this review.

## 8. Limits of this review

This review does not prove the global optimality of 332 or 333 unknowns, historical novelty, consistency of ZFC, or a new internal Lean/Rocq endpoint. It does not establish a 332- or 333-unrestricted-integer result: all these variables range over the nonnegative integers. The new argument is a complete arithmetic reduction whose final logical calibration composes with the explicitly retained ordinary C222/refutation proofs.

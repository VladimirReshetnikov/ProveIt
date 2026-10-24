# Independent audit of the CRT carrier

The new ordinary reduction and both literal CRT polynomials pass this
independent audit. The audit uses no builder import. Its exact algebraic
results are in `CRT_CHECK.json` and `CRT_CHECK_OPTIMIZED.json`; the audit
script is `peer_crt.py`.

The rational centered form has 161 live operations and exact degree 768.
The integral centered form has 154 live operations and exact degree 784.
Every displayed front expression has an independent free-ring identity
check. The complete generic centered four-root identity has 1,890 terms,
all compared with the separately multiplied conjugates. Independent
leading induction through every actual DAG gate proves the attained
coefficients stated in the producer metadata; no numerical sampling is
used to establish the degrees.

## Scope of the mathematical review

The changed front is Y=qv. Set M=2q^2, D=MH,
Kstar=X(2X-3c)-2, B=MKstar+H(v-q^2), z=DT+B,
A=(z^2+3D^2)(z^3-19D^3), S=srM^5H.
The first, strong, auxiliary and guard registers otherwise have the
same formulas as the scalar12 parent. The centering is n_old=n+V
in the rational auxiliary equation and n_old=n+delta V in the integral
auxiliary equation.

The following are the crucial dependency and exceptional-branch checks.

1. q is even and 2 modulo 3, and |X|>=64. For v=0, a=0,H=3,Delta=3.
   For v nonzero, |a|=|qv(X+1)|>=1008, so Delta=(a+2)^2-1>1.
   Thus H is always nonzero and odd, M is positive, D is nonzero, and
   delta=Delta^2 I^2-1 is never zero. The initially admitted v=0 branch
   is not silently omitted.
2. H=3 modulo q and 3 does not divide q. Therefore gcd(H,q)=1 and,
   since H is odd, gcd(H,M)=1. This cancellation does not involve I.
3. Modulo 3, a=H=Delta=0 and Df=1. Since X=-1 modulo 3,
   ell=XY^2 is either 0 or -1 modulo 3, so Dt=1 for every v, including
   v=0. Also delta=Cy=-1. These are exactly the prime-order facts needed
   to separate the auxiliary, strong, first and guard radicals.
4. S=0 is equivalent to sr=0, because M,H are nonzero. It implies
   I=Q=0 and delta=Cy=-1. All scaled radicals and all center shifts
   vanish, leaving A^16. But A=D^5 pi(z/D), where pi(x)=(x^2+3)(x^3-19)
   has no rational zero. Thus s and r are nonzero at every final zero.
5. The fixed-prime separation proof can now be used even if c=0 or
   the guard radicand was initially negative. It yields rational roots
   for every term and integer roots of Df,Dt,Dg. Dg>=0 and s!=0 force
   Pair>0. The joint guard gives eta*zeta>0, whereas c=0 would give
   -Y(Y+1)k^2<=0. Therefore c!=0 before any strong-rank theorem is
   invoked. Then I!=0,Q>1, and adjacent-coefficient Pell descent makes
   the auxiliary root integral. This order handles all initial zero
   and sign branches without an odd-multiplier assumption.
6. The integral conjugate relation, including either polynomial center
   shift, gives S|A. Hence M^5|A and H|A. For a prime p^e exactly
   dividing M, suppose v_p(z)=b<e. Since v_p(D)>=e, in
   A=z^5+3D^2z^3-19D^3z^2-57D^5 the leading term has valuation 5b
   strictly smaller than every other term. It cannot cancel and is
   below 5e, a contradiction. Therefore M|z.
7. Reducing z modulo M and canceling the unit H gives M|v-q^2.
   Consequently v=q^2(2u+1), and Y=q^3(2u+1). Thus the full original
   large odd-cubic source scale is recovered BEFORE the parent's
   pre-projection Pell and native bounds are used. In particular the
   initially possible v=0 branch is now excluded by proof.
8. Reducing A modulo H gives H|(MKstar)^5. Since gcd(M,H)=1,
   H|Kstar^5. The weaker-congruence argument in reduction12/PROOF.md
   now applies exactly: Kstar=2Kold-HXc, H odd; the signed main index
   folds before this projection; and the actual beta makes
   |H|>|(sigma X-2^R)(2^R sigma X+1)|^5. Thus sigma X=2^R, and the
   original signed source kernel is restored.

## Completeness

For a canonical parent witness take v=q^2(2u+1), where u is its original
odd-cubic input. The canonical main projection gives H|Kstar, and
M|v-q^2. Therefore D=MH divides B exactly: each summand
MKstar and H(v-q^2) is a multiple of MH. Put kappa=B/D.

Choose the same guard witnesses and the same fixed strong pair I,f as
in the retained full-residue interpolation theorem. Intersectivity gives
a residue T with I|pi(T+kappa), and the auxiliary interpolation realizes
that residue without changing I. Then

A=D^5 pi(T+kappa),
A/S=H^4 pi(T+kappa)/(sr)=c^2 H^4 pi(T+kappa)/I,

which is an integer. The total norm-center n is chosen last, subtracting
V or delta V to account for the selected centering. This is the same
unbounded existence argument as the parent with a new integer shift
kappa. No coprimality of H and I, surjectivity of pi modulo I, or selection
of I after the residue is needed. The zero guard root is permitted.

The accepted endpoint remains the parent's ordinary native/refutation
calibration. This audit does not add a Lean theorem or reprove that
calibration by finite computation. No mathematical defect was found in
the changed CRT carrier or its two centered equations.

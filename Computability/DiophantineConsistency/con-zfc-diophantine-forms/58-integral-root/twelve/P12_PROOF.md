# A degree-629 equation in twelve positive integers

This is a local mathematical reduction of the authentic normalized blank
compiler, and a new twelve-positive-variable tradeoff. It uses 114 live binary
operations (all +, -, * charged), compared with the wave-7 degree-897/108-operation
lean equation. Three equations have maximum residual degree 622 and 109
operations, or 108 after the inherited positive transport shift. No minimum
claim or end-to-end proof-assistant certificate is asserted.

## 1. Coefficient and completeness restriction

Use one complete authentic four-port tuple (beta,K0,MC,MF), with beta=B-1,
B=2^d and d odd, and MF already shifted by B-1. The compact source39/44 tuple
has d=590069. The authentic canonical compiler uses N=lambda^n with lambda odd,
hence N odd; its old coordinate Jold=(B^N-1)/(B-1) is 1 mod 3, because B=2 mod3.
For a nontrivial canonical computation N>1, Jold>1. Therefore setting
Jold=3J+1 preserves existence; soundness is immediate from the affine map.
The ordinary compiler can supply arbitrarily large odd prime-power N, so the
unimportant N=1 exceptional value is avoided in canonical completeness.
Now q=beta Jold+1=2 mod3. The complete tuple itself is not changed.

## 2. Literal equation

Quantified variables: J,F,alpha,z,h,i,T,s,w,eta,zeta,t, all strictly positive.
Every other letter is an abbreviation. Define

  j=3J+1, q=beta j+1, C=q-F-alpha,
  X=wq, Y=sq, E=XY, k=eta+zeta, c=kY+eta,
  a=E+Y, H=4a+3, Delta=a^2+H=(a+2)^2-1,
  ell=EkY, A=1+ell(ell+k), G=1+Delta c^2, b0=X+ac,
  R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)j,
  Nk=k-hE-R, Nt=(K0+w)C+q-F-z(q-1),
  I=ic^2, D=1+Delta I^2, Q=(Delta I)^2, d0=Q-1,
  v=cT, b=c+RD, e=Q(Dv^2+b^2)-1, Baux=2Qvb,
  S=q^2 H, L=q^2(1+HIT),
  W=q^2 b0+H[q^2(t+b+ell)+s].

Use d0 for the polynomial d-register to distinguish it from the fixed compiler
bit-width d. Define the invariant formal norm

  N=product_{g=±sqrt(G), tau=±sqrt(A), f=±sqrt(D)}
       [d0(W-Lg-S tau)^2-S^2 e+S^2 Baux f].

This is an ordinary integer polynomial: every formal sign is included, and
there is no claim that the signs are independent automorphisms after numerical
specialization. The final equation is

  Nk Nt (1+N)-1=0.

Its literal division-free evaluator is p12_desaturated_product.json, generated
by build_p12.py. The generic evaluator is the predecessor's exact quadratic-
remainder norm identity; check_p12.py independently multiplies the eight
formal factors in an eight-dimensional algebra.

## 3. Outer recovery before recovering q^3 divisibility

The generic norm is a square modulo4, by the predecessor remainder identity.
Consequently a product root has N=0 and Nk=Nt=epsilon in {1,-1}. Authentic
native coefficient inequalities, using Nt a unit, give

  C>=0, q-F=C+alpha>0, q>=16, 3q<R<q^4-2.

Here Y is only sq. Do not yet use q^3|Y or E>R. Instead use

  X>=q, Y>=q, E>=q^2, k=hE+R+epsilon>R,
  c>kY>RY, a+2<2E, I>=c^2, c>96.

Write g=sqrt(G), f=sqrt(D), tau=sqrt(A) for positive real roots when making
bounds. Then g<2Ec, f<2EI and

  1<A<Delta c^2<=Delta I=sqrt(Q).

The algebraic strict inequality A<Delta c^2 is exactly the inherited estimate
Delta c^2-A>k^2[EY(2Y^2-1)+Y^4]-1>0, valid already for Y>=16.
Also d0>0.5 E^4 I^2, c<I^2 and D<4E^2 I^2 imply

  b+cf < (4R+1) E^2 I^2,
  (b+cf)/d0 < 9R/E^2.                         (1)

The exact identity (Ig)^2-(cf)^2=I^2-c^2 gives

  Ig-cf=(I^2-c^2)/(Ig+cf)>I/(8Ec)=ic/(8E).   (2)

Since c>RY and X,Y>=16,

  icE>RYE=RXY^2>72R.

Combining (1)-(2) gives Ig-cf>(b+cf)/d0. This is the only extra estimate
needed to remove the old hypothesis E>R from the outer branch argument.

For any coherent auxiliary root y, with f'=±sqrt(D),

  d0 y^2=Q(vf'-b)^2-1,

the predecessor triangle/square estimate gives

  |y|<b+Tcf+T(b+cf)/d0<b+ITg,
  |tau'+y|<tau+b+ITg.

The negative-main-root branch of N=0 would instead have

  (W+Lg)/S=b+ITg+(t+s/q^2)+ell+(b0+g)/H.

Here t+s/q^2>0, tau<ell+k, and (b0+g)/H>c/3>k because Y>=16.
This branch exceeds tau+b+ITg, a contradiction. Actual quadratic conjugation
therefore forces g to be rational, hence a positive integer, and
x=(W-Lg)/S is rational.

## 4. Inner roots and the new divisibility

The predecessor exceptional-root proof uses only 1<A<sqrt(Q), already proved.
It reconstructs rational f',tau' with (f')^2=D, (tau')^2=A, hence integer f',tau'.
The rational Pell saturation lemma then makes y=x-tau' an integer: for integer
m>=2,V and rational y, m^2 V^2-(m^2-1)y^2=1 implies y integral. Apply it to
m=Delta I and V=vf'-b, now an integer. Thus x is integral.

Reducing W=Lg+Sx modulo q^2 gives q^2|Hs. Since Y=sq,

  H=4sq(X+1)+3=3 mod q.

As q=2 mod3, gcd(q,H)=1. Thus q^2|s. Put sold=s/q^2, a positive integer.
Then Y=sold q^3, restoring the ordinary compiler's original scale. Dividing
W=Lg+Sx by q^2 gives

  b0+H(t+b+ell+sold)=(1+HIT)g+Hx,

so g=b0 mod H and gamma=(g-b0)/H is an integer. Moreover k>E follows
from Nk=epsilon and R>1. Hence c>kY>XY^2>X; using g>(a+1)c gives gamma>0.

Now all equations of the inherited normalized signed compiler are satisfied,
with Jold=j, sold=s/q^2, main ordinate c, and integral main root g. The
normalized-to-ordinary map i_ordinary=Delta*i gives exactly the signed ordinary
strong and auxiliary equations. Its common-unit theorem forces epsilon=1 and
extracts a blank K215 halt. This is the same inherited signed-quotient boundary
used in the source12 and source11 lean equations; no new signed theorem is
assumed. The order matters: q^2 divisibility is recovered before using E>R,
main-index recovery, or compiler population arguments.

## 5. Completeness and positivity

Choose canonical positive normalized compiler witnesses with odd N>1. Keep
F,alpha,z,h,i,T,w,eta,zeta and set

  J=(Jold-1)/3, s=sold q^2,
  t=gamma+ITg+tau+y-b-ell-sold.

Every expression is integral. The standard auxiliary inequality y>=b-vf and
the strict identity Ig>cf give

  t>=gamma+T(Ig-cf)+(tau-ell)-sold.

Since ell>k, tau<ell+k,

  tau-ell=(ell k+1)/(tau+ell)>k/3.

Canonical Nk=1 gives k>E=XY; therefore

  k/3>XY/3>Y/q^3=sold

because X>=q>=16. Thus t>0. Its definition makes the desired norm factor
zero. The source units are +1, so the product vanishes. Both existence
directions are proved, without assuming Con(ZFC).

## 6. Exact degree

Put q0=3 beta J, X0=w q0, Y0=s q0, E0=X0 Y0, k0=eta+zeta,
c0=k0 Y0, I0=i c0^2, ell0=E0 c0, H0=4E0,
Q0=E0^4 I0^2, R0=q0^3(q0-F), B0=R0 E0^2 I0^2, V0=I0 T ell0.
The respective total degrees are

  H0:4, ell0:7, Q0:30, B0:26, V0:15, c0:3.

First omit q^2 scaling and the rational offset sold=s/q^2. The exact
cancellation analysis of the inherited lean norm is homogeneous under these
weights. Its eight coherent leading factors have degrees

  79,79,79,79,71,71,67,65,

whose sum is590. Specifically four opposite f/g branches have leaders
-sg*4 H0^2 Q0 B0 V0; two tau-negative matched branches have leader
4 H0^2 Q0 B0 ell0; the remaining matched negative-g branch has leader
H0^2 Q0 B0 c0; the final matched positive-g branch has leader
H0^2 Q0 B0 [2t-k0-iT c0/E0]. The rational expression multiplies a sufficiently
large monomial to make the entire leading form polynomial. The last bracket
is nonzero because t is independent. The resulting leading form is

  2^12 H0^16 Q0^8 B0^8 V0^4 ell0^2 c0
       [2t-k0-iT c0/E0].

For the actual norm, there is an exact identity in the localization at q:

  N=q^32 Nlean(t+s/q^2).

The rational shift has degree -1, so cannot change the degree-one leading
carrier term. The scale adds32 degrees. Hence degN=622. Nk has degree5,
with leader -hE0, and Nt has degree2, with leader
w(q0-F-alpha)-zq0, a nonzero polynomial. The product therefore has exact
degree629 for every authentic beta>0.

## 7. Finite checks and limits

check_p12.py checks 60 modular formal-norm identities and full polynomial
rays at three different primes for both formal-port fixtures and the actual fixed tuple; all six give norm degree622 and productdegree629. It also checks 59 modular substitution identities against the pinned old norm, all four coefficient payload hashes, and fourteen source-file pins.
The checker uses only Python's standard library. Modular polynomial products
use exact Kronecker packing with base strictly greater than
min(len(a),len(b))*(p-1)^2, the bound on every unreduced convolution
coefficient. Consequently no carries can mix coefficient positions. It
cross-checks this routine against a separate naive convolution on 24
deterministic fixtures. Every verification gate raises an explicit exception,
so optimization does not remove checks; normal and `-O` runs give identical
receipts. The six ray results are unchanged from the prior NumPy-based
implementation.
Those finite checks independently corroborate the transcription and degree
lower bound, not the unbounded semantic compiler theorem. The degree upper
bound and equivalence are the preceding mathematical arguments.

## 8. Bundled dependency map

- `upstream/LEAN_PROOF.md`: package52 complete lean construction, especially
  Sections3-4 (root recovery), Section7 (leading cancellation), and Section7a
  (the twelve-positive predecessor theorem).
- `upstream/INNER_RECOVERY_PROOF.md`: package44 exceptional-root and generic norm proof.
- `upstream/ELEVEN_POSITIVE_PROOF.md`: package38 rational Pell saturation proof.
- `upstream/ORDINARY_BLANK_PROOF.md`: inherited signed compiler and calibration boundary.
- `upstream/positive12_none_lean_product.json`: the exact predecessor polynomial.
- `upstream/build_absorbed.py`, `upstream/check_absorbed.py`: unmodified predecessor builder and checker, retained as inert references.
- `SOURCE_PINS.json`: all fourteen exact source paths, commit, Git blobs and SHA-256 hashes.
- `../coefficients/COEFFICIENT_BINDING.json`: authoritative whole-tuple binding.

Only the local authored builder and checker are run; no upstream Python module is executed.

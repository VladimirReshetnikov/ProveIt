# Fifteen and sixteen unrestricted integers

Research derivation at ProveIt commit `8c6eec9d19ef80538c8e61ff6e0180040583446a`.
The fixed coefficient tuple and normalized quartic are exactly those of
`29-simpler-forms/signed17/upstream/`: the original T4 tuple, without rebinding.
All statements below are ordinary mathematics formalizable in ZFC. The imported
compiler and Jones source interface remain dependencies; no new end-to-end
Lean/Rocq certificate is claimed.

## 1. Imported literal Jones body

Use the complete body in `upstream/nine/nine_section.tex`, equivalently Section 1
of the delivered signed17 proof, with nu=32 and L=5^33. Its fixed index constants
are z=2^s and y=e_*(2z). The strict weighted coefficient bounds imply

    0 < y < (2z)^(L+1),   z >= 2.

Every digit of e_* lies in [1,2z-1], and its exponent is between 0 and L, which
proves this inequality directly by the geometric sum bound. Set

    Bfloor = (2z)^(L+1).

This is a new fixed, explicitly prescribed integer coefficient; the y leaf drops out of the fifteen-variable DAG. Since
z is a power of two, Bfloor is a power of two. It is not an unknown.

For the sixteen-variable form keep b=y+1+epsilon. For the fifteen-variable form
replace this with

    b=Bfloor*r^2.

The eight integer base coordinates are respectively

    (epsilon,g0,h0,s0,w0,phi,i0,j0),
    (r,g0,h0,s0,w0,phi,i0,j0).

Set g=g0+1,h=h0+1,s=s0+1,w=w0+1,i=i0+1,j=j0+1, and use the same body:

    B=b^5; q=B^L; ell=sum_(t=1)^32 B^(5^t);
    lambda=sum_(t=0)^(4L-1) B^t; e=e_*(B); theta=B-2z;
    N=q^16; Gcap=32b B^(5^32);
    R=[g+e q^3+ell q^5+
      (2(e-z lambda)(1+B+g)^4+lambda B+lambda Bq^4)q^7](N^2-N)
      +[q^3-b ell+ell+theta lambda q^3+(B-2)q^8](N^2-1);
    U=N^2w; Y=N^2s; M=RY; P=2M^2U; K=R+1+h(P-1);
    A=M(U+1); B1=2R+1; W1=bw; C=B1+W1+phi;
    J=4A-5; Q=3W1C-2(W1^2-1);
    D=(A^2-1)C^2+1; E=iJDC^2; F=(A^2-1)E^2+1;
    G1=A+F(CD+1-A); H=B1+jC; I=(G1^2-1)H^2+1;
    a0=(P^2-1)K^2+1; a1=DFI;
    m=K^2Gcap-4(C-KY)^2Gcap-8gK^2;
    D0=JF; T0=QF+J(H-C).

The imported source equivalence says that, with all eight original coordinates
nonnegative, the conditions a0,a1 integer squares, D0|T0, m>0 are solvable iff
the pinned normalized quartic is solvable, iff K215 has a blank halting run,
iff a finite ZFC refutation exists.

## 2. Cofinal power-of-two completeness

The source reduction has the following strengthened completeness statement:
given a particular solution of the normalized quartic, the Jones ratio conditions
can be constructed with b=2^w for every sufficiently large w.

Here is the exact source-level justification, not an inference from mere
existence. `Master3.lean`, theorem `USys_of_mem`, begins with a quartic witness
tuple zs, chooses w=x*y+sum(zs)+1 and b=2^w, and uses that choice only to obtain
1<=w, x*y<b, and zs_i<b. Replace that choice by any w at least the displayed
value; all three inequalities and every subsequent step of the proof remain
valid. The remaining definitions q,lambda,theta,e,ell,g and the transfer, tau,
and packing arguments use b and these inequalities, never the equality defining
w. `NineReduce.reduced_of_mem` merely transports these witnesses, retaining b.
`NineRatio.ratio_complete` likewise takes b as an input and preserves it.
Consequently any cofinal subsequence of power-of-two ceilings can be used in
the completeness direction.

Write Bfloor=2^k0. For any sufficiently large t, set r=2^t. Then
b=Bfloor*r^2=2^(k0+2t) belongs to such a cofinal subsequence. Thus restricting
the ceiling to this form loses no quartic solution. Conversely, r!=0 implies
b>=Bfloor>y, so epsilon=b-y-1 is a nonnegative integer and exactly reconstructs
the original source ceiling. A zero of the new formula need not assume that
b is a power of two: the source ratio soundness theorem derives that property
from the ratio conditions. This distinction is necessary.

This strengthened completeness lemma is newly extracted from the displayed
ordinary construction. The existing Lean theorem is not itself a theorem with
the stronger universal quantifier over w, and no compiled proof of that
strengthening is claimed.

## 3. Positivity already encoded in the body

The following facts, proved in signed17, remain valid independently of j:

* D0 is nonzero for every integer assignment. J=4A-5 cannot vanish. If F=0,
  then A=0,E=+/-1, but E=iJDC^2 is divisible by 5 at A=0, a contradiction.
* The five ratios a0,a1,D0,T0,m are invariant under i -> -i. Hence an i!=0
  can be replaced by |i|, making i0 nonnegative.
* If b>y, g,s,w>=1, phi>=0, a0 is a square and m>0, then R>=2, K>0,
  and h>=1. For clarity, m>0 yields g<Gcap/8 and
  4(C-KY)^2<K^2. The former bound proves R>=N^2-N by the source's explicit
  positive-bracket estimate. Hence C>0, U,Y>=1, P>=2R^2>R+2.
  The latter bound excludes K<=0. If h<=0 then 1<=K<=R+1<P.
  K=1 would imply P-1 divides R, impossible; 2<=K<P puts a0 strictly
  between (PK-1)^2 and (PK)^2. This contradicts squarehood.

The full inherited argument is in `inherited/SIGNED17_PROOF.md`, Lemmas 1--3. It needs
only b>y, not the original linear parameterization of b or a sign on j.

## 4. New Pell orbit lemma

Let t>=2, Delta=t^2-1, H an arbitrary integer, and suppose

    a^2-Delta*H^2=1

for an integer a. Given any integer modulus M>=1 and bound L0>=0, there are
integers a',H' such that

    a'^2-Delta*H'^2=1, H'>L0, H' congruent H modulo M.

Proof. Choose a>=1 by changing its sign. Delta is positive and nonsquare.
The unit eta=t+sqrt(Delta)>1 has matrix

    T = [[t,Delta],[1,t]] in SL_2(Z).

Its reduction modulo M has a finite order k>=1 (M=1 is harmless). The real
number beta=a+H*sqrt(Delta) is positive even when H<0, since
a>|H|*sqrt(Delta). The vector (a_n,H_n)=T^(kn)(a,H) consists of integers,
has norm one, and is congruent to (a,H) modulo M. Moreover

    H_n=(beta*eta^(kn)-beta^(-1)*eta^(-kn))/(2sqrt(Delta)) -> +infinity.

Choose n large enough. No assumption that eta is the fundamental unit is used.
The proof covers H=0 and negative H.

## 5. The j guard is redundant

Assume the five sixteen-variable base guards epsilon,g0,s0,w0,phi>=0
(or the four fifteen-variable guards g0,s0,w0,phi>=0 and r!=0), together
with i!=0 and the source ratio conditions. The previous section gives
R>=2,U,Y>=1,A>=4,C>0,D>1,E!=0,F>1. Since C>=1 and A>=4,

    CD+1-A >= A^2+1-A > 0,

so G1=A+F(CD+1-A)>1. Thus all of D,F,I are positive, with I>=1.

These three integers are pairwise coprime:

    F == 1 (mod D),    F == 1 (mod J),
    G1 == 1 (mod D),   I == 1 (mod D).

As gcd(J,F)=1, divisibility JF|QF+J(H-C) gives F|H-C. In addition
G1==A (mod F), so

    I == (A^2-1)C^2+1 == D (mod F).

Hence gcd(F,I)=gcd(F,D)=1. Therefore the square a1=DFI forces each of
D,F,I to be a positive integer square. In particular I is a square.

Apply the Pell orbit lemma with t=G1, modulus M=C*F, and L0=B1+C.
It produces H'>B1+C, H'==H (mod CF), and I'=(G1^2-1)H'^2+1 a square.
Define j'=(H'-B1)/C. This is an integer greater than 1 because
H'==H==B1 (mod C). Replace j by j'. The quantities B1,C,J,D,E,F,G1,
a0,m do not depend on j and remain unchanged. The new a1'=DFI' is a square;
T0'-T0=J(H'-H) is divisible by JF. Thus all source ratio conditions survive,
and j0'=j'-1 is nonnegative.

No degenerate C=0,D=0,F=1,G1<=1 case enters the argument: the guards and
positive margin established the displayed strict inequalities first.

## 6. The shortened guard stack

For the sixteen-variable form use five guards x=(epsilon,g0,s0,w0,phi)
and six unrestricted integer witnesses z1,...,z6. For the fifteen-variable
form use four guards x=(g0,s0,w0,phi) and five witnesses z1,...,z5.
Write k for the number of base guards (k=5 or k=4). Set C0=1 and

    d_t=3x_t+2,
    B_t=1+4d_t C_(t-1)^2 z_t^2,
    C_t=C_(t-1)B_t            (1<=t<=k),
    d_(k+1)=3m-1,
    B_(k+1)=1+4d_(k+1)C_k^2 z_(k+1)^2,
    Cstar=C_k B_(k+1).

Each B_t is 1 modulo 4 and coprime to all earlier factors. If every z_t
is nonzero, Cstar is an integer square iff all x_t>=0 and m>0 can hold
with appropriate z_t. Necessity follows by unique factorization and
B_t==1 mod4, which excludes negative square factors. Sufficiency uses a
nontrivial Pell solution for each positive nonsquare d_t==2 mod3 whose
second coordinate is divisible by 2|C_(t-1)|. Such solutions exist by
the same finite-order unit argument. This is precisely the inherited
coprime Pell stack with one or two unnecessary guards removed.

Every assignment, before any condition is known, satisfies

    Cstar == 1 (mod 4), Cstar != 0.

Consequently the new smaller weight w1=Cstar+1 satisfies
|w1|>sqrt(|Cstar|). If Cstar>=1 this is immediate; otherwise Cstar<=-3
and |Cstar+1|=|Cstar|-1>sqrt(|Cstar|).

## 7. The literal polynomial

Let Pi(t)=(t^3-t-1)(t^2+23), and define

    Rhom(D,T,v)=((T+Dv)^3-D^2(T+Dv)-D^3)
                *((T+Dv)^2+23D^2).

The inherited intersectivity lemma proves that for D!=0,

    D|T and Z!=0  iff  exists v in Z: ZD^5 | Rhom(D,T,v),

and Rhom(D,T,v) is never zero. Its proof uses the cubic discriminant -23,
Hensel lifting and CRT; the converse is a direct least-valuation argument.

For sixteen variables let Z=i*z1*...*z6. For fifteen variables let
Z=r*i*z1*...*z5. Put

    S=Z D0^5; T=Rhom(D0,T0,v); X=S*u-T;
    w1=Cstar+1; w2=w1(P^2+K^2+2);
    A0=S^2 Cstar; A1=S^2 w1^2 a0; A2=S^2 w2^2 a1;
    V=X^2+A2-A0-A1; W=V^2+4X^2 A2-4A0 A1;
    F=W^2-16V^2X^2 A2.

The requested equation is F=0. All named quantities are polynomial
abbreviations, with no additional existential variables. The inputs count is
8+(k+1)+2, hence sixteen or fifteen unrestricted integers.

The norm identity is unchanged:

    F=product_(sigma0,sigma1,sigma2 in {+1,-1})
       [X-S(sigma0 sqrt(Cstar)+sigma1 w1 sqrt(a0)+sigma2 w2 sqrt(a1))].

Weights may be signed. Only their absolute values matter. The universal bound
sqrt(|a0|)<=P^2+K^2+1 and |w1|>sqrt(|Cstar|) yield

    |w2|>sqrt(|Cstar|)+|w1|sqrt(|a0|).

A rational signed root sum can therefore be fixed by every multiquadratic
Galois automorphism only if each nonzero root is fixed: at the greatest changed
coordinate, its contribution has magnitude at least its weight and strictly
exceeds all earlier contributions. Thus all roots are rational, hence integers.
The argument covers negative candidate radicands and zero roots. S=0 is excluded
by F=T^8!=0. It follows that zeros are equivalent to S!=0, S|T, and Cstar,a0,a1
integer squares. The converse chooses the integer u=T/S+sqrt(Cstar)+w1sqrt(a0)
+w2sqrt(a1).

Apply the stack, intersectivity, i/h normalization, and new j normalization.
For fifteen variables apply also the cofinal-ceiling completeness lemma.
The result is exactly solvability of the pinned Jones source. Thus for each
of F15,F16, ZFC proves

    [there is no unrestricted-integer zero of F] iff Con(ZFC).

## 8. Exact degree and operation counts

The fast body uses the division-free radix-five ladders and multivariate Horner
factorization of package27, folding identical and literal coefficient recipes.
These are algebraic identities in every integer assignment, independent of the
semantic guard arguments. The original T4 tuple and its weighted coefficients
are retained coherently.

The new division-free DAGs have:

| Equation | Integers | Binary operations | Exact degree |
| --- | ---: | ---: | --- |
| F16 | 16 | 1550 = 655 add + 26 sub + 869 mul | 406528*5^33+10008 |
| F15 | 15 | 1541 = 651 add + 26 sub + 864 mul | 813056*5^33+4184 |

Constants are fixed leaves; each binary addition, subtraction and multiplication,
including scalar multiplication and squaring, is charged. Fixed power evaluation
is expanded into multiplication nodes. Shared reuse is free. Construction of
fixed constants is not included in the variable arithmetic count.

For F16, deg(Cstar)=2221L+1102, deg(S)=34375L+107,
deg(w2)=4121L+1110 and deg(A2)=101632L+2502. A2 strictly dominates
X^2,A0,A1, so the leading term of F16 is A2^4. The certificate propagates a
nonzero diagonal leader independently of all fixed coefficients.

For F15, deg(Cstar)=4442L+374, deg(S)=68750L+107,
deg(w2)=8242L+382 and deg(A2)=203264L+1046. Again the leader is A2^4.
The diagonal leading coefficient is a nonzero integer times a fixed positive
power of Bfloor. The certificate tracks that monomial symbolically; no modular
sample is used to assume that Bfloor itself is nonzero.

The 15-variable equation improves the concrete delivered 17-integer equation
by two variables and 19066 binary operations, at increased degree. The
16-variable option lowers the old degree as well. These are improvements within
the compared repository constructions, not a global optimality theorem or a new
universal representation bound.

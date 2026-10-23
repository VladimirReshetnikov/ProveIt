# Fourteen unrestricted integers, and a lower-degree fifteen-integer form

These are the recommended signed constructions of this package. Earlier
sixteen/seventeen-variable intermediate constructions are superseded here.
Both equations below have unsolvability provably
equivalent in ZFC to Con(ZFC). The proofs are mathematical, not newly compiled
Lean or Rocq certificates. No global minimum is asserted.

## Shared definitions and coefficients

Use the exact Jones source registers and three-root finalizer in
the shared lemmas below. The source quartic has31 positive variables; L=5^32.
Every weighted coefficient is fixed by INDEX_CONSTANTS.json, using the whole
coefficient tuple in ../coefficients/payloads/COEFFICIENT_BINDING.json.
The new index is z=2^4259933. Set

 Bodd=2(2z)^(L+1)=2^[1+4259934(L+1)].

This is a fixed integer, not an unknown. Its exponent is odd, since L+1
is even. The index theorem gives y=e_*(2z)<(2z)^(L+1)<Bodd.
Bodd and y are specified by exact bounded recipes, not materialized as
full binary strings. All four native coefficient ports and z are materialized.

## The fourteen-variable polynomial

The unknowns are exactly

 (epsilon,g0,h,s0,wroot,phi,i,j,z1,z2,z3,z4,residue,normroot) in Z^14.

In the Jones source definitions set

 b=Bodd epsilon^2, w=wroot^2,
 g=g0+1, s=s0+1; h,i,j are unrestricted coordinates directly.

The other registers through a0,a1,m,Ddiv,Tdiv are unchanged. Guard only
x1,x2,x3=(g0,s0,phi):

 d_r=3x_r+2 (r=1,2,3), d4=3m-1,
 C0=1, B_r=1+4d_r C_(r-1) z_r^2, C_r=C_(r-1)B_r,
 Cstar=C4, Z=epsilon wroot i z1 z2 z3 z4.

Define the complete finalizer by

 S=Z Ddiv^5, r=Tdiv+Ddiv residue,
 T=(r^3-Ddiv^2 r-Ddiv^3)(r^2+23Ddiv^2),
 w1=Cstar, w2=Cstar(P^2+K^2+2), X=S normroot-T,
 A0=S^2 Cstar, A1=S^2 w1^2 a0, A2=S^2 w2^2 a1,
 V=X^2+A2-A0-A1, W=V^2+4X^2 A2-4A0A1.

The equation is

                    F14=W^2-16V^2 X^2 A2=0.

This is fully specified by signed14.json, with1586 binary operations:
684 additions,26 subtractions,876 multiplications. Its exact degree is

                    813056*5^32+2152.

There are80 nonliteral fixed leaves after aliases and integer constants
are folded. Polynomial register abbreviations do not increase the14
quantified-variable count.

## Why the square w restriction is complete

The source Ratio.exists_B25core (pinned Ratio.lean.txt, necessity section)
chooses, for b=2^k,

                    w=2^(2R+1-k).

The exponent is strictly positive: b<=R implies k<2^k=b<=R<2R+1.
The cofinal packing proof permits arbitrarily large exponents k of either
parity. In Master3.USys_of_mem lines312–320, the selected exponent is used
only to infer b>xy and that every quartic witness coordinate is below b;
the rest of the proof uses these inequalities and b=2^k, not the special
formula for that exponent. NineReduce propagates the same b unchanged. Our Bodd has odd exponent a, and choosing epsilon=2^t gives
k=a+2t odd. Therefore2R+1-k is even and the canonical w is a positive
square. Choose wroot=2^((2R+1-k)/2). All subsequent constructions in
exists_B25core and NineRatio.ratio_complete preserve that w.
This argument uses the exact canonical w formula; it does not assert that
arbitrary Pell witnesses may be required to be squares.

For soundness, the finalizer implies S!=0, hence epsilon,wroot,i and all
z_r are nonzero. Consequently b>Bodd-1>y and w>0. The guard stack gives
g,s positive, phi>=0 and m>0. The h-positivity proof in the shared lemmas below
uses only these statements, not any j condition, so h>0 as before.

## Why the j guard is unnecessary

The signed-H proof included below extends the product-Pell
soundness lemma to arbitrary signed H=B+jC. Its hypotheses hold here:
R>0,A>1,B=2R+1>1 is odd,C=B+bw+phi>=B,J=4A-5>0 and i!=0.
The quotient condition JF|QF+J(H-C), together with gcd(J,F)=1,
gives J|Q and F|H-C. The signed-H lemma recovers C=psi_A(B), even
when j is negative. Its key step reflects a negative Pell index modulo
4t1, using M_A^(4t1)=identity modulo chi_A(t1).

The original positive product-Pell completeness theorem then supplies
fresh positive i',j' for the same A,B,C,J. Thus D F' I' is square and
F'|H'-C. Since J|Q is unchanged, JF'|QF'+J(H'-C) follows.
Neither a0 nor m depends on i,j. Therefore the recovered signed solution
can be replaced by an ordinary positive-i,positive-j Jones ratio solution.
All other coordinates, including the restricted square w, are unchanged.
The ordinary ratio soundness theorem applies.

Conversely, the cofinal odd-exponent packing construction gives a ratio
solution with square w and positive i,j. The linear-prefix stack supplies
four nonzero guard variables, the intersective lemma supplies residue,
and the three-root finalizer supplies normroot. These arguments prove both
directions of the refutation/solution equivalence. Negation gives

 ZFC proves (there is no integer zero of F14) iff Con(ZFC).

## A lower-degree equation in fifteen integers

Keep b=y+1+epsilon, with epsilon guarded rather than squared, but still
set w=wroot^2 and release j. Guard the four coordinates
(epsilon,g0,s0,phi) and m, using five z variables. Set
Z=wroot i z1 z2 z3 z4 z5. The remaining definitions are unchanged.
This gives signed15_linear.json, with1594 operations
(688 additions,26 subtractions,880 multiplications) and degree

                    406528*5^32+2528.

Completeness chooses a sufficiently large odd k in the free-base packing
proof, then epsilon=2^k-y-1>=0. The canonical w is again a square.
Soundness needs only b>y and w>0; it does not require an independently
asserted parity of k. Using h,i,j directly rather than h0+1,i0+1,j0+1 is an affine bijection
on unrestricted integers and saves three gates without changing degree.
This form has roughly half the degree of F14,
at the cost of one additional integer variable and eight operations.

## Exact degree certificates

For F14 the named degrees are:

 m:4442L+14; Cstar:4442L+58; Ddiv:13750L+29;
 S:68750L+152; w2:8242L+68; A2:203264L+538.

A2 strictly dominates X^2,A0,A1, and the second term in the final
subtraction has smaller degree than A2^4. On the diagonal its leading
coefficient is2^832*12^120*Bodd^(406528L+8), which is nonzero.
For F15linear the corresponding output coefficient is2^832*12^248,
and deg(A2)=101632L+632. These give the stated exact degrees for the
actual coefficients, not merely generic degree bounds. The independent
modular checks supplement these exact mathematical leading-term arguments.

## Evidence and limitations

check_signed_forms.py regenerates each circuit from inert source data,
checks source-register equality on signed inputs, and independently computes
the finalizer as an8-by-8 multiplication-matrix determinant. Finite guard,
intersectivity and divisibility tests are included. The universal proofs,
not the finite tests, establish equivalence. No actual ZFC refutation or
halting witness is searched for, and no consistency claim is made.

Further reductions would require proving a further sign restriction is
redundant or a further canonical witness lies in a polynomially parameterized
subfamily. Neither arbitrary square substitution nor finite testing would
justify such a step.

## Complete shared Jones source registers

B=b^5, q=B^L, ell=sum_{r=1}^{31}B^(5^r),
lambda=sum_{r=0}^{4L-1}B^r, e=e_*(B), theta=B-2z,
N=q^16, Gcap=32b B^(5^31),

R=[g+e q^3+ell q^5+
   (2(e-z lambda)(1+B+g)^4+lambda B+lambda B q^4)q^7](N^2-N)
  +[q^3-b ell+ell+theta lambda q^3+(B-2)q^8](N^2-1).

U=N^2w, Y=N^2s, M=RY, P=2M^2U,
K=R+1+h(P-1), A=M(U+1), B1=2R+1, W1=bw,
C=B1+W1+phi, J=4A-5, Q=3W1 C-2(W1^2-1),
D=(A^2-1)C^2+1, E=iJDC^2, F=(A^2-1)E^2+1,
Gp=A+F(CD+1-A), H=B1+jC, I=(Gp^2-1)H^2+1,
a0=(P^2-1)K^2+1, a1=DFI,
m=K^2 Gcap-4(C-KY)^2 Gcap-8gK^2,
Ddiv=JF, Tdiv=QF+J(H-C).


## Shared algebraic lemmas

## 2. Linear-prefix square stack

For any integer assignment, every B_r and C_r is1mod4, hence nonzero,
and gcd(B_r,C_(r-1))=1. Thus all factors B_r are pairwise coprime.
If all z_r!=0 and Cstar is an integer square, each |B_r| is a square.
As B_r=1mod4, a negative B_r cannot be a signed negative square, so every
B_r is a positive square. All prefix C_r are consequently positive.
If any d_r<0, its factor would be <=-3, a contradiction. No d_r vanishes
because d_r=2mod3. Hence d_r>0: all guarded x_j>=0 and m>0.

Conversely, suppose these inequalities hold. Inductively C_(r-1) is a
positive square. The positive integer d_r is2mod3 and nonsquare, so
d_r C_(r-1) is nonsquare. Choose a nontrivial Pell solution
u^2-d_r C_(r-1) v^2=1 with v even (a suitable positive power of a Pell
unit has even second coordinate). Put z_r=v/2!=0. Then B_r=u^2 and
C_r is a positive square. This constructs the guard list.

When S!=0, all z_r!=0. Each d_r is nonzero and each prefix nonzero,
so B_r!=1; since B_r=1mod4, |B_r|>=3. Therefore |Cstar|>=3^r>1, where r is the number of guards.
This observation permits the smaller signed separation weight w1=Cstar.

## 3. Divisibility and nonvanishing

For every integer base assignment Ddiv!=0. Indeed J=4A-5!=0. If F=0,
then (A^2-1)E^2=-1 forces A=0,E=+/-1, but E=iJDC^2 is then divisible
by5, impossible.

The polynomial Pi(t)=(t^3-t-1)(t^2+23) has no rational root and has a
root modulo every positive integer. The cubic is monic and neither1
nor-1 is a root; the quadratic has no real root. For odd primes p!=23,
either the cubic has a simple root, or it is an irreducible cubic whose
Frobenius three-cycle fixes a square root of its discriminant -23;
then the quadratic has a simple root. Lift by Hensel. At23 the cubic's
root3 is simple. At2 the quadratic lifts because -23=1mod8. Apply CRT.

For nonzero D and arbitrary integer T0,Z,

 D|T0 and Z!=0  iff  exists v: ZD^5 | (r^3-D^2r-D^3)(r^2+23D^2),
 r=T0+Dv.

The right-hand polynomial never vanishes, since it equals D^5 Pi(T0/D+v).
If D|T0, intersectivity supplies v modulo |Z|. Conversely Z=0 would
force a zero. If p-adic valuations satisfy v_p(T0)=beta<alpha=v_p(D),
then v_p(r)=beta, the cubic and quadratic factors have valuations3beta
and2beta respectively, so their product has valuation5beta<5alpha,
contradicting divisibility byD^5. Apply with D=Ddiv,T0=Tdiv.

## 4. Three-root finalizer with signed small weights

The polynomial F is identically the product of the eight factors
X-S(e0 sqrt(Cstar)+e1 w1 sqrt(a0)+e2 w2 sqrt(a1)), e_r in{-1,1}.
Complex square roots are allowed in this formal identity. T is neverzero.
If S=0, then F=T^8!=0. Hence every zero has S!=0.

On this locus, |w1|=|Cstar|>sqrt(|Cstar|). Also, for arbitrary real P,K,
sqrt(|(P^2-1)K^2+1|)<=P^2+K^2+1. Therefore
|w2|>sqrt(|Cstar|)+|w1|sqrt(|a0|).
Distinct sign patterns of the nonzero roots have distinct sums: the
largest differing root has magnitude at least1 (its square is a nonzero
integer), and its weighted contribution dominates all earlier ones.
If F=0, one sum equals normroot-T/S, a rational number. Every Galois
automorphism of the field generated by these roots changes their signs;
the separation forces it to fix each root. Each root is rational, and
then integer since its square is integer. Thus Cstar,a0,a1 are squares
and S|T. This argument does not assume independent square classes and
works for initially negative radicands. Conversely those square and
divisibility conditions allow normroot=T/S+r0+w1r1+w2r2.

## 5. Removing the h and i sign restrictions

The guards and square w give g,s,w positive, phi>=0,m>0, b>y and i!=0.
Replacing i by |i| changes none of a0,a1,Ddiv,Tdiv,m: i occurs through
E and thereafter only E^2. Hence i can be taken positive.

To show h>0, m>0 implies K!=0, g<Gcap/8=4b B^(5^31), and
4(C-KY)^2<K^2. Since b>y, B>2z and B>=32. With t=5^31,
1+B+g < B^(t+2)<=q and b ell<q. These bounds make both brackets
defining R positive (the positive lambda B q^4 absorbs
2z lambda(1+B+g)^4). Thus R>=N^2-N>=2. Consequently C>0,Y,U>=1,
P>=2R^2>R+2. The strict approximation forces K>0. If h<=0, then
1<=K<=R+1<P. K=1 would imply P-1|R, impossible. For2<=K<P,
(PK-1)^2<(P^2-1)K^2+1<(PK)^2, contradicting a0 square. Hence h>=1.


## Removing the Jones j-positivity guard by signed index reflection

Let A,B,C,J be positive integers with A>1, B>1, B<=C, J>0,
and assume 2B<=C or B is odd. Let i be any nonzero integer and j any
integer. Define

D=(A^2-1)C^2+1, E=i J D C^2, F=(A^2-1)E^2+1,
G=A+F(CD+1-A), H=B+jC, I=(G^2-1)H^2+1.

Suppose DFI is an integer square and F divides H-C. Then
C=psi_A(B), where psi_A is the Pell sine sequence with recurrence
psi_A(n+2)=2A psi_A(n+1)-psi_A(n), psi_A(0)=0, psi_A(1)=1.

## Proof

Replacing i by |i| leaves D,F,G,H,I unchanged. Thus E may be assumed
positive. The standard product-Pell argument gives D,F,I positive,
G>1, and pairwise coprime D,F,I. Indeed F=1 modulo D, G=1 modulo D,
I=1 modulo D, G=A modulo F, and H=C modulo F imply I=D modulo F.
Hence all three factors are positive squares.

The Pell parametrization supplies nonnegative indices t0,t1,t2 with
C=psi_A(t0), E=psi_A(t1), |H|=psi_G(t2). As in the pinned
ProductPell proof, C^2|E implies C|t1; also t1>=2, 1<=t0<=t1,
and F=chi_A(t1)^2. Set k=chi_A(t1)>0.

If H>=0, the original proof applies verbatim: H=psi_G(t2),
psi_A(t2)=C modulo k, and t2=B modulo C. The usual Pell
index-congruence lemma gives B=t0 or B=-t0 modulo C, and the
productPell_index lemma gives C=psi_A(B).

If H<0, then psi_A(t2)=-C modulo k. Let
M=[[2A,-1],[1,0]]. The determinant of M is1 and the trace of M^t1
is2chi_A(t1)=0 modulo k. Cayley-Hamilton therefore gives
M^(2t1)=-Id modulo k, and M^(4t1)=Id modulo k. Choose a positive
integer Q large enough that n=4t1 Q-t2>=0. The inverse-matrix
identity for the Pell sine coordinate gives

    psi_A(n)=-psi_A(t2)=C modulo k.

Since G=1 modulo C, psi_G(t2)=t2 modulo C. Thus H=-psi_G(t2)
implies -t2=B modulo C. As C|t1, the reflected index satisfies
n=-t2=B modulo C. Apply the same ordinary index-congruence lemma
now to n in place of t2. Its conclusions are n=t0 or n=-t0
modulo C, so again B=t0 or B=-t0 modulo C, and the unchanged
productPell_index conclusion follows. This proof does not require
j>=0 or H>=0. The case H=0 causes no issue for the nonnegative
branch; alternatively F>C and F|H-C exclude it.

## Application to the Jones ratio conditions

Retain the guards on g,s,w,phi and the positivity consequence for h.
They imply R>0,A>1,C>=B=2R+1>1, with B odd. Keep i!=0 but drop
the guard j0>=0: put j=j0+1 with j0 an arbitrary integer.
From JF|QF+J(H-C) and gcd(J,F)=1, derive J|Q and F|H-C.
The signed-H lemma yields C=psi_A(B). The standard constructive
product-Pell theorem then supplies fresh positive i',j' for these
same A,B,C,J. Their F',H' satisfy F'|H'-C. Together with J|Q this
restores JF'|QF'+J(H'-C), and D F' I' is square. The radicand a0
and margin m do not depend on i,j, so they remain unchanged.
Thus any signed-j ratio solution can be replaced by a genuine
positive-j ratio solution. Completeness is immediate because the
original positive witnesses are still allowed.

This removes one guard witness from the coprime Pell stack. It uses
ordinary Pell theory and matrix arithmetic, not a newly compiled
formal theorem. The exact source proof inspected is
Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/ProductPell.lean,
psi_of_ProductPellConds and productPell_index, at commit
8c6eec9d19ef80538c8e61ff6e0180040583446a.

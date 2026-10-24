# Denominator-free three-root transport: eleven positive variables, degree 277

Status: complete ordinary mathematical proof, with a literal division-free
circuit and exact algebraic replay. The independent review is recorded separately.
This composition removes a denominator guard from source 70 by applying the adjacent-coefficient Pell descent proved in source 69. Exact source copies and pins are recorded in this component. The inherited native/compiler and weighted-carrier interfaces remain dependencies.

## 1. Inherited interface and fixed numerals

Use exactly the fixed compact44 numerals beta, K0, MC, MF from the parent
component, with the already-shifted MF payload. They are fixed integers, not
witnesses. Write B = beta + 1 = 2^590069. The pinned upstream is ProveIt
9cca523d9f27ad39d52993f4065cbd7e58f8bdd4. The source of the normalized positive
Pell interface and its canonical solutions is package 61, especially its
report's positive auxiliary reconstruction lemma, `lem:auxcomplete`.

We use the weighted transport theorem proved in `upstream/source70_weighted_carrier.tex`
and the preceding section of the combined report: the four residuals
A0, A1, As, Aa defined below have a positive
solution precisely when the source Diophantine system does. Soundness holds
for every positive integer weight hstar. Canonical completeness holds for
any such weight hstar >= k, including weights computed after the strong and
auxiliary Pell roots have been chosen. The inherited source system has a
solution iff there is a finite ZFC refutation; its machine/compiler/calibration
dependencies are unchanged here.

For reference, that theorem uses

    A0 = Z^2 - M^2 Dtau,
    Z = M(ell+k+r)+(q-1)Y-q^3 W Bt,
    As = f^2 - Delta (i_old c^2)^2 - 1,
    Aa = (V+u)^2 - Delta(f^2-1) u(2V+u) - 1,
    V = f^2(cT-R)-c,
    W = 1+(q-1)hstar.

The remaining residual A1 is reproduced in Section 2. In every canonical
source solution, t=Bt/(q-1)=q(z_source-1) >= q, s=Y/q^3 satisfies 0<s<k,
and the positive first Pell root tau satisfies ell<tau<ell+k. Thus the
transport variable can be chosen as

    r = Wt + tau - ell - k - s > q W - 2k.

The same source has q>=16, R>=3, R=3 mod 4, c=psi_(a+2)(R), and the positive
auxiliary reconstruction lemma applies to *every* positive Pell solution
f^2-Delta I^2=1 with c|I. It supplies positive T and u, with y=V+u>0 and
the displayed auxiliary equation. No fixed value of the strong Pell index
is demanded by that lemma.

## 2. Explicit polynomial registers

The eleven unknowns, all strictly positive integers, are

    j, F, alpha, i, T, X, Y, n, eta, zeta, gamma.

Define the following integer polynomial registers, with no divisions:

    J = 3j+1;                   q = beta J+1;
    C = q-F-alpha;              E = XY;
    k = eta+zeta;               c = kY+eta;
    a = E+Y;                    H = 4a+3;
    Delta = a^2+H = (a+2)^2-1;  ell = E kY;
    R = ((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J;
    Rhat = q^3(q+F+alpha);
    M = q^3(q-1);
    Bt = (q K0+X)C-qF;
    Dtau = ell(ell+k)+1;
    I = i c^2;
    Df = 1+Delta I^2;
    Q = Delta(Df-1) = Delta^2 I^2;
    delta = Q-1;
    V = Df(cT-R)-c;
    Dnum = Q V^2-1;
    Vbar = Df(cT+Rhat);
    L = 3 Vbar;
    W = 1+(q-1)L;
    Zbar = M(ell+k+n+L)+(q-1)Y-q^3 W Bt;

The adaptive main Pell carrier is

    r0 = k-R-1;
    S = 4qY;                   U = qS = 4q^2Y;
    Dstar = U(X+ac)+H(U gamma+SX-r0);
    A1 = Dstar^2-U^2(1+Delta c^2).

For the three-root norm, use

    A = M^2 Dtau;
    Bf = M^2 Df;
    Cnum = M^2 Dnum;
    Ncenter = delta^2 ((Zbar^2-A-Bf)^2-4 A Bf)
              -2 delta Cnum (Zbar^2+A+Bf)+Cnum^2;
    N8 = Ncenter^2-64 delta^3 A Bf Cnum Zbar^2.

The literal circuit evaluates the same norm center using the smaller
factored schedule Tn=delta^2 A Bf, Rn=delta Cnum,
Jn=delta(Zbar^2-A-Bf)-Cnum, Ncenter=Jn^2-4(Tn+Rn(A+Bf)),
N8=Ncenter^2-64 Tn Rn Zbar^2.

The one-equation presentation is

    P11 = N8+A1+N8 A1 = (1+N8)(1+A1)-1 = 0.

In proof only, write Dy=Dnum/delta. Dy is generally a rational number
before the norm is imposed; no division appears in the polynomial.

## 3. Unconditional radical separation and positive guard

All assertions here hold for every positive input tuple; none assumes C>0,
q^3|Y, an index equality, or any equation.

We have q>1, k>=2, c>=3, a>=2, Delta>=15, I>=c^2, and

    ell < ac,   k<c,
    1<Dtau<Df<Q.

Indeed, ell(ell+k)<a(a+1)c^2<Delta I^2. The last inequality follows
from I>=c^2 and Delta>a(a+1). Also Q=Delta(Df-1)>Df.
Set t=sqrt(Dtau)>0 and f=sqrt(Df)>0. Then

    t < ell+k < (a+1)c,
    f > (a+1)I >= (a+1)c^2 >= 3c^2.

Put b=cT-R, an integer. If b=0 then V=-c. If b>=1 then
V>=Df-c>1; if b<=-1 then V<=-Df-c<-1. Consequently |V|>1
in all cases, and

    Dy = V^2+(V^2-1)/(Q-1) > V^2 > 1.

Let y=sqrt(Dy)>0. The three positive rational radicands Dtau,Df,Dy
are pairwise distinct. Dtau<Df was proved above. If Dy were either integer
D in {Dtau,Df}, then Q(D-V^2)=D-1, impossible because 0<D-1<Q.

There is moreover strict dominance by one root. If b=0, then Q>c^2
implies Dy<c^2+1 and y<c+1. But

    f-t > (a+1)c(c-1) > c+1,

so f>t+y. If b!=0, then |V|>=Df-c. The bound f>3c^2 implies
f^2-c>2f (since f>c+2), while f>t. Hence

    y>|V|>=Df-c>2f>f+t.

Thus no signed sum +/-t +/-f +/-y is zero.

The positive polynomial L is an unconditional bound for f+y. The authentic
fixed masks have 0<MC<beta and 0<MF<2beta, hence
(MC+q MF)J<(q-1)(1+2q)<2q^2. Since q>=16 and alpha>=1,

    |R| < q^4+Fq^3+(alpha+2)q^2 < q^3(q+F+alpha)=Rhat.

Indeed, the final difference is positive because alpha(q-1)>2. As the gap
Rhat-|R| is a positive integer and Df>c,

    |V| <= Df(cT+|R|)+c < Df(cT+Rhat)=Vbar.

Also

    Vbar > Df > f,
    Dy = V^2+(V^2-1)/(Q-1)<2V^2,

so y<2|V|<2Vbar. Therefore L=3Vbar>f+y and L>c>k.

## 4. Rational sum of three radicals

Lemma. Suppose d1,d2,d3 are positive rationals, pairwise distinct, and no
signed sum of their positive square roots is zero. If a signed sum of the
three roots is rational, then all three roots are rational.

An elementary extraction proof. Let signed roots x1,x2,x3 have rational
nonzero sum t and squares a,b,c, respectively. Set

    u=(t^2-a-b-c)/2,
    v=(u^2-ab-ac-bc)/(2t).

The identities u=x1*x2+x1*x3+x2*x3 and v=x1*x2*x3 give

    x1 = a(a+u)/(at+v),
    at+v = x1(x1+x2)(x1+x3).

The latter denominator is nonzero: x1 is nonzero, and a cancellation
x1=-x2 or x1=-x3 would contradict distinctness of the radicands. Thus
x1 is rational, and the cyclic formulas give the other two roots.
This proof uses only rational identities. QED.

An alternative square-class proof. Partition the roots by their classes
in Q*/Q*^2. Square roots from
different classes are linearly independent over Q; this follows, for
example, by applying the character idempotents of the finite multiquadratic
Galois group to any proposed linear relation. Thus in a rational sum,
the contributions from every nontrivial square class must sum to zero.
A nontrivial class containing one root cannot do this. A class containing
two roots can cancel only when the corresponding positive roots are equal,
contrary to distinctness of the radicands. A nontrivial class containing
all three roots can give a rational sum only if that sum is zero, contrary
to the hypothesis. These exhaust the partitions of three terms. This proof
does not assume that the three square classes are independent. QED.

For completeness, character independence follows by taking the field
generated by the finitely many square roots in the relation. Each class
present gives a distinct quadratic character on its Galois group. If
sigma(sqrt(d))=chi_d(sigma)sqrt(d), averaging chi_d(sigma)*sigma(relation)
over the group isolates the coefficient of that class; orthogonality of
distinct characters makes all other averages zero.

## 5. The norm equation and integrality recovery

For indeterminates x,a,b,c the exact universal identity is

    F8(x;a,b,c)
      = [(x^2-a-b-c)^2-4(ab+ac+bc)]^2-64abc x^2
      = product_(epsilon in {+1,-1}^3)
          (x-epsilon1 sqrt(a)-epsilon2 sqrt(b)-epsilon3 sqrt(c)).

This can be verified by multiplying the eight conjugate factors in the
quadratic extension ring. With the positive rational radicands
A=M^2 Dtau, Bf=M^2 Df, Cnum/delta=M^2 Dy, the integer register N8
is exactly delta^4 F8(Zbar;A,Bf,Cnum/delta).
All eight roots are real. N8=0 therefore yields signs with

    Zbar/M = tau_* + f_* + y_*,
    tau_*^2=Dtau, f_*^2=Df, y_*^2=Dy.

By Section 3 and the radical lemma, the three signed roots are rational.
Because Dtau and Df are integers, rational-square integrality gives
tau_*, f_* in Z. The auxiliary root y_* is rational. It satisfies

    Q V^2-(Q-1)y_*^2=1.

The following adjacent-coefficient descent, independently proved in source69,
now gives y_* in Z. No coprimality with M is needed.

**Descent lemma.** For an integer Q>1 and integer V, every rational y with
Q V^2-(Q-1)y^2=1 is an integer. To prove this, replace V,y by absolute values;
neither is zero. Write y=a/m in lowest terms. Then m^2 divides Q-1. If V=1,
y=1. For V>1 use

    V'=(2Q-1)V-2(Q-1)y,
    y'=(2Q-1)y-2QV.

V' is integral, the same norm is preserved, and y>V and QV>(Q-1)y give
-V<V'<V. The norm excludes V'=0. Since 2Q-1=1 modulo m, y' has exactly
the same reduced denominator m. Strong induction on the positive integer |V|
therefore reaches V=1 without changing m, whence m=1. This proof applies
before any C>0, transport integrality or strong index recovery.

Recover positive witnesses

    i_old = i,
    f_old = |f_*|,
    y_old = |y_*|,
    u = y_old-V,
    r = n+L-f_*-y_*.

Section 3 gives y_old>|V|, so u>0. It also gives L>|f_*|+|y_*|,
so r>0 for every choice of signs. Finally

    Z = Zbar-M(f_*+y_*) = M tau_*

is exactly the first carrier register with this r and hstar=L.
The equation for Dy is equivalent to

    y_old^2-Q(y_old^2-V^2)=1,

so A0=As=Aa=0. Together with A1=0 this is a positive solution of the
weighted carrier interface, hence produces a finite ZFC refutation.
The signed f_*,y_* MUST be used in the recovered r; their absolute values
are used only for the strong and auxiliary witnesses.

## 6. Completeness without the denominator guard

Start with a canonical source solution (equivalently, a finite refutation
and the inherited canonical source construction). Fix its outer quantities
q,X,Y,k,c,a,R,tau and coefficient witnesses. Use its positive normalized
strong Pell pair f,I with c^2 dividing I; set i=I/c^2>0. This is exactly
the inherited source strong equation, so no additional congruence restriction
or finite-group strengthening is necessary. Alternatively the matrix-order
argument of source70 may be used with modulus c^2 alone.

The inherited positive auxiliary reconstruction lemma applies to this
chosen f,I because c|I and the outer source has R=3 mod 4 and
c=psi_Aparam(R). It gives positive T,u and y=V+u. Now compute
Rhat,Vbar,L,W from these already-chosen values. This order of choices
avoids a dependence loop: strong pair, then auxiliary pair, then L,W,
then the first transport variable.

Choose r=Wt+tau-ell-k-s as in Section 1. Since t>=q, s<k and
tau>ell, we have r>qW-2k. Because q>=16 and L>=k,

    qW-2k = q+q(q-1)L-2k > L.

Consequently n=r-L+f+y>0. By construction
Zbar=M(tau+f+y), so N8=0. The adaptive main carrier lifts via
the preceding weighted theorem, choosing its positive gamma, and A1=0. The other
eleven inputs are positive; J=3j+1 follows from the canonical repunit
choice with the same fixed beta. Thus P11=0.

## 7. A single equation without squaring the degree

N8=Ncenter^2-64*(integer), so N8 is 0 or 1 modulo 4. Since 4|U,
A1=Dstar^2-U^2*(integer) is also 0 or 1 modulo 4.
If (1+N8)(1+A1)=1, the two integer factors are both 1 or both -1.
The second case would make both residuals -2, impossible modulo 4.
Thus P11=0 iff N8=A1=0. The converse is immediate. This is an
unrestricted integer factorization argument, so no positivity of the
residuals is being assumed.

## 8. Exact degree and a nonzero leading coefficient

The exact degrees, checked by the literal circuit audit, are
I:5, Df:14, Q:18, V:18, Rhat:4, L:18, W:19, Zbar:24,
A:16, Bf:22, Cnum:62, Ncenter:132, N8:264, A1:13, P11:277.
Use q0=3 beta j and k0=eta+zeta. The leading forms are

    Bt0=(K0 q0+X)(q0-F-alpha)-q0 F,
    Df0=i^2 k0^4 X^2 Y^6,
    Q0=i^2 k0^4 X^4 Y^8,
    Rhat0=q0^3(q0+F+alpha),
    L0=3 i^2 q0^3 k0^4 X^2 Y^6(q0+F+alpha),
    Zbar0=-3 i^2 q0^7 k0^4 X^2 Y^6(q0+F+alpha) Bt0,
    N8_264=Q0^4 Zbar0^8,
    A1_13=32 q0^2 k0 X^2 Y^4(4 q0^2 Y gamma+q0^3(q0-F)).

The last formula uses cancellation of the apparent degree-14 terms of
the adaptive Pell residual; the exact audits check that cancellation independently.
The degree-277 form of P11 is the product of these last two forms:

    2^5 3^8 i^24 q0^58 k0^49 X^34 Y^84 (q0+F+alpha)^8 Bt0^8
       * (4q0^2 Y gamma + q0^3(q0-F)).

In it, the coefficient of

    j^60 i^24 eta^49 X^42 Y^85 alpha^16 gamma

is exactly 2^7*3^8*(3 beta)^60 > 0. The gamma term fixes the last factor;
minimum j-degree reduces (q0+F+alpha)^8 Bt0^8 to
X^8(F+alpha)^16, whose alpha^16 coefficient is 1.
The total degree of this monomial is 277. Both exact audits validate the
cancellation contract and this selected coefficient; mere generic
gate-degree propagation would be insufficient.

## 9. Scope and comparison

The complete division-free DAG has eleven strictly positive unknowns,
exact degree 277 and 111 live binary operations, comprising 65 multiplications,
29 additions and 17 subtractions. The two residuals use 108 operations.
This improves source70's 325/113 endpoint by deleting the q(q-1) denominator
guard using source69's descent, not by modifying the counting convention.
All scalar multiplications and squares are charged; fixed numeral leaves
and reuse are free. No statement of global optimality or world-first novelty
is made. Nine-positive universal encodings already exist at much larger degree.

The new step is an ordinary mathematical composition. The complete native
compiler, weighted Pell interface, source calibration and literal ZFC
consistency predicate remain inherited. Finite exact algebra and coefficient
checks do not prove those unbounded semantic interfaces or Con(ZFC).

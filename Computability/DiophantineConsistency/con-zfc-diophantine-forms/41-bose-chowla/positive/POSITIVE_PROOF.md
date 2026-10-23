# A degree-938 equation in twelve positive unknowns

This is a new reduction of the existing normalized blank-K215 interface.
The source pin is `22e75dd6b87b1b199bb08c778d7cf075ae5aae08` in
VladimirReshetnikov/ProveIt. Let `BASE` denote
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms`.

## Sources and precise proof boundary

The inherited complete coefficient tuple is source 31's tuple, with
`beta=beta`, `K0=K`, `MC=MC`, and **shifted** `MF=MF_source`, from
`BASE/31-sun10/signed10/data/coefficients_binding.json`. The four gzip
payloads are already included in the parent deliverable at
`upstream/source31/signed10/data/`. This construction does not use
`beta_sun`, the Jones/Sun index, or any mixed coefficient tuple.

The source-31 tuple's complete normalized interface is proved in
`BASE/31-sun10/coefficients/COEFFICIENT_PROOF.md`. The positive norm
arguments are uniform in any complete tuple satisfying that interface:
`BASE/34-integer14/report/synthesis_report.tex`, section "A lower degree
twelve variable norm", explicitly states that uniformity. Its
`positive/upstream/sections_positive.tex` reproduces source 24's sharper
auxiliary estimate and rational Pell saturation. Source 37's
`positive/section.tex` proves the complete coordinate change
`w_old=w+q`. All these are ordinary mathematical proofs; the present
construction does not claim a fresh Lean/Rocq certificate.

The inherited mathematical interface is the following. For one authentic
complete tuple, the two weak transport equations `Nk=Nt=epsilon`, where
epsilon is 1 or -1, imply, before any algebraic-root recovery,

\[
q\ge16,\quad X\ge q,\quad Y\ge q^3,\quad E=XY,\quad
3q<R<q^4-2,\quad E>R+2,\quad k=R+\epsilon+hE>E,
\]
\[
kY<c<k(Y+1),\qquad \sqrt G-\sqrt A>kY^2.
\]

Recovering integer roots `g,tau,f,y`, a positive `g`, and the main
congruence `g=b0 mod H`, with the normalized four Pell equations below,
recovers a halting blank K215 computation and forces epsilon=1. Conversely
a halting computation has a canonical positive normalized witness,
including positive `g,tau,f,y,gamma`; the main exponent satisfies
`X=2^R`. The already proved calibrated machine theorem equates this
halting assertion to a finite ZFC refutation. The source-31 coefficient
proof, not finite tests, supplies the compiler part of these assertions.

## Polynomial, domain, and fixed coefficients

The supplied unknowns are exactly

\[
J,F,\alpha,z,h,i,T,s,w,\eta,\zeta,t\in\mathbb Z_{>0}.
\]

All subsequent symbols are polynomial abbreviations. Define

\[
\begin{aligned}
q&=\beta J+1,&\omega&=w+q,&C&=q-F-\alpha,\\
X&=\omega q,&Y&=sq^3,&E&=XY,\\
k&=\eta+\zeta,&c&=kY+\eta,&a&=E+Y,\\
H&=4a+3,&\Delta&=a^2+H,&\ell&=EkY,\\
A&=1+\ell(\ell+k),&G&=1+\Delta c^2,&b_0&=X+ac,\\
R&=((q-1)(q-F)+\alpha)(q^2-1)+(M_C+qM_F)J,\\
N_k&=k-hE-R,&N_t&=(K_0+\omega)C+q-F-z(q-1),\\
I&=ic^2,&D&=1+\Delta I^2,&Q&=(\Delta I)^2,&d&=Q-1,\\
v&=cT,&b&=c+RD,&e&=Q(Dv^2+b^2)-1,&B_1&=2Qvb.
\end{aligned}
\]

The new low-degree majorant and the carrier are

\[
\boxed{M=k(ik^3+T)^2},\qquad \delta=(a+2)c-\ell,
\]
\[
\sigma=b+M\delta+v(a+2)I,\quad
L=HM+1,\quad W=b_0+H(t+\sigma).
\]

Define the integer polynomial

\[
N=\prod_{\tau=\pm\sqrt A,\;g=\pm\sqrt G,\;f=\pm\sqrt D}
\left[d(W-HM\tau-Lg)^2-H^2e+H^2B_1f\right].
\]

All signs in this formal product are independent. Conjugate multiplication
makes it an integer polynomial even when radicands vanish, are squares,
or generate coincident quadratic fields. It is evaluated by the scalar
trace/remainder circuit in `build_majorant.py`, with no algebraic-number
arithmetic or additional quantified variables.

The equation and system are respectively

\[
\boxed{N_kN_t(1+N)-1=0},\qquad
\boxed{N_k=1,\quad N_t=1,\quad N=0}.
\]

They have exactly twelve positive unknowns. The former has degree 938 and
122 binary arithmetic operations; the latter has maximum residual degree
929 and 117 operations. Every binary +,-,* counts, including multiplication
by a numeral; sharing is free and the system compares its two final norm
terms directly.

## The new separator lemma

We prove the replacement of the previous degree-23 separator by the
degree-9 polynomial M. All quantities in this argument satisfy the
authentic weak interface. The shifted X obeys

\[
X=q(w+q)\ge q(q+1)>q^2,\qquad R<q^4<X^2.
\]

Moreover

\[
c<\tfrac{17}{16}kY,\quad a+2<\tfrac{17}{16}E,\quad k>E,
\quad Y\ge q^3\ge4096.
\]

An essential sharper bound is

\[
\boxed{\frac{R(a+2)^2c^4}{k^8Y^2}<1.}\tag{1}
\]

Indeed, its left side is equal to the following expression, which is bounded by

\[
\frac{R}{X^2}
\left(\frac{a+2}{E}\right)^2
\left(\frac{c}{kY}\right)^4
\left(\frac E k\right)^4
\le
\left[
\frac q{q+1}(1+q^{-2}+2q^{-5})(1+q^{-3})^2
\right]^2.
\]

For q>=16, put x=q^-2. The product of the two parentheses is at most
`(1+2x)(1+x)^2=1+4x+5x^2+2x^3 < 1+5x < 1+1/q`.
The bracket is therefore strictly less than one. The displayed comparison
is an elementary inequality, not a syntactic polynomial-degree argument.

Write `Z=v sqrt(D)+b`. Every complex auxiliary root satisfying

\[
dy^2=Q(vf-b)^2-1,\qquad f^2=D
\]

obeys

\[
|y|<Z+v+1.\tag{2}
\]

Here is a direct proof of the inherited sharp estimate. Since
`Delta>R+2` and `I^2>=c^4`,
`Q-b=Delta I^2(Delta-R)-c-R>0`, so `b<=d`. Also
`sqrt(D)<Delta I<d`. Thus

\[
|y|^2\le\frac{QZ^2+1}{d}
<\left[Z\left(1+\frac1d\right)\right]^2,
\]

because the difference of the last two expressions is
`(QZ^2-d)/d^2>0`. Finally `Z/d<v+1`, proving (2).

Since `D<(a+2)^2 I^2`, inequality (1) implies

\[
\frac b{kY^2}<i^2k^7+1.
\]

Also

\[
\frac{v\sqrt D}{kY^2}
<\frac{(a+2)iTc^3}{kY^2}
<\left(\frac{17}{16}\right)^4 EYiTk^2
<\frac{(17/16)^4}{X}iTk^4<iTk^4.
\]

The last step uses `k>E=XY` and `X>=256`. We have
`v/(kY^2)<T` and `1/(kY^2)<1`. Consequently

\[
\frac{Z+v+1}{kY^2}<i^2k^7+iTk^4+T+2
<i^2k^7+2iTk^4+kT^2=M.\tag{3}
\]

The final strict inequality follows from `k>=2`, `i,T>=1`.
Equations (2)--(3) prove

\[
|y|<MkY^2<M(\sqrt G-\sqrt A),\qquad |y|<M\sqrt A.
\]

In fact `sqrt(A)>ell=XkY^2`, so (3) also proves the stronger
completeness estimate `M sqrt(A)>X Z>2Z`.

## Soundness

The scalar trace/remainder identity implies N is a square modulo 4.
Explicitly, writing `Tr=2x0`, `Kn=x0^2-4d^2W^2L^2G`, its final norm is
`ur^2-Tr ur vb+Kn vb^2`, congruent to `(ur-x0 vb)^2` modulo 4.
At a zero of the product polynomial, all three integer factors are units.
`1+N=-1` would mean `N=-2`, impossible modulo 4. Hence N=0 and
`Nk=Nt=epsilon` for a common epsilon in {1,-1}. The system gives
epsilon=1 directly.

A vanishing norm factor gives coherent algebraic roots with

\[
x=(W-Lg)/H=M\tau+y,
\quad \tau^2=A,\quad g^2=G,\quad f^2=D,
\quad dy^2=Q(vf-b)^2-1.
\]

Work in a finite normal splitting field over Q. Every conjugate of x has
absolute value less than `M sqrt(A)+MkY^2<M sqrt(G)` by the separator
lemma. If g were irrational, an automorphism changing its sign would
produce two x values at distance `2L sqrt(G)/H>2M sqrt(G)`, a
contradiction. Thus g is rational and, since g^2 is integral, integral.
The quantity x is now rational. If tau were irrational, conjugation would
change `M tau` by magnitude `2M sqrt(A)`; two auxiliary roots of magnitude
strictly less than `M sqrt(A)` cannot compensate. Therefore tau is
rational and integral; y is rational; and `f=(e-dy^2)/B1` is rational
and integral because B1>0 and f^2=D.

The rational Pell saturation lemma applies to

\[
(\Delta I)^2(vf-b)^2-((\Delta I)^2-1)y^2=1
\]

and yields integral y, hence integral x. The saturation lemma is the
standard Pell fact proved in source 24: if S>=2 and V are integers and
`S^2 V^2-(S^2-1)y^2=1` with rational y, then y is integral. Its proof
reduces the denominator to a common Pell unit and uses divisibility of
the cosine sequence to force an odd multiple of the index.

Because sigma>0, W>0. A negative g would give
`x=(W+L sqrt(G))/H>M sqrt(G)`, impossible. Thus g>0. Modulo H,
`W=b0` and `L=1`, so g=b0 mod H. The quotient gamma is integral and
positive: `g>(a+1)c`, `c>X`, and `b0=X+ac` imply `g>b0`.
All normalized Pell and transport conditions have now been recovered;
the ordinary strong coordinate is `i_ord=Delta*i`.
The inherited signed-quotient compiler theorem gives a blank K215
halting computation and epsilon=1.

No independent-radical Galois automorphisms were assumed: each
contradiction uses only an automorphism whose existence follows from the
irrationality of the particular square root.

## Completeness

Take a canonical positive normalized compiler witness. Its original
coordinate obeys `w_old=X/q=2^R/q>q`, since `R>3q`. Thus `w=w_old-q`
is a positive integer, proving completeness of the new coordinate
change. Set

\[
t=\gamma+M(g+\tau)+y-\sigma
=\gamma+M(g-\delta)+M\tau+y-b-v(a+2)I.
\]

This is an integer. Furthermore
`ell/c>E/2>2`, so `0<delta=(a+2)c-ell<ac<g`.
Also `(a+2)I<2 sqrt(D)` and the separator lemma gives
`M tau>2(v sqrt(D)+b)>v(a+2)I+b`. Therefore t>0.
The identity `W=Lg+H(M tau+y)` makes one norm factor vanish, and
Nk=Nt=1. Both presentations therefore have a positive solution.

Combining both directions and the calibrated K215 endpoint proves, by
ordinary mathematics formalizable in ZFC,

\[
\mathrm{ZFC}\vdash
\bigl[\neg\exists\mathbf x\in\mathbb Z_{>0}^{12}\ P(\mathbf x)=0\bigr]
\leftrightarrow\operatorname{Con}(\mathrm{ZFC}),
\]

and the analogous statement for the three-equation system. This is an
equivalence, not a consistency proof or a global minimum claim.

## Exact degree and the nonzero leading form

Scale all twelve variables by a formal parameter and work over their
rational-function coefficient field. Put q0=beta J, k0=eta+zeta,
omega0=w+q0, Y0=s q0^3, E0=omega0 q0 Y0, c0=k0Y0. The common degrees are

|Quantity|E,H|c|I|D|Q,d|b|sqrt(A),sqrt(G)|sqrt(D)|M|v|
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
|Degree|6|5|11|34|46|38|11|17|9|6|

Let the positive-leading roots be tau,g,f. The standard Laurent expansions
give

\[
g-\tau=\delta-k/2+O(\lambda^{-1}),\qquad
f_0-f=I/(2(a+2))+\text{terms of lower degree},\quad f_0=(a+2)I.
\]

The second difference has exact degree 5 and leading form I0/(2E0).
For each g,tau sign, let

\[
C_{s_a,s_g}=b_0+Ht-s_g g+HM(\delta-s_a\tau-s_g g)+Hv(f_0-f).
\]

Its exact degrees are 26,26,24,17 for sign pairs
`(+,+),(-,-),(+,-),(-,+)`, respectively. The last degree is 17 because
`HM(delta+tau-g)` has degree 16, below `Hv(f0-f)`.

The four f=+sqrt(D) factors have degree 119. In the four negative-f
factors, the degree-119 auxiliary terms cancel, and the leading terms
are `2dHb C_{sa,sg}`. All other terms have degree at most 104.
Their degrees are therefore 116,116,114,107. The norm degree is

\[
4\cdot119+2\cdot116+114+107=929.
\]

Multiplying the nonzero leading factors gives the exact homogeneous form

\[
\boxed{
N_{929}=-2^{46}i^{43}k_0^{103}T^5s^{152}
\omega_0^{69}q_0^{549}(q_0-F)^8.
}
\]

It is nonzero for every authentic fixed beta>0. The degrees of Nk and Nt
are 7 and 2, with leading forms `-hE0` and
`omega0(q0-F-alpha)-zq0`. Hence the product degree is exactly 938.
Finite checks in `CHECK_RESULTS.json` reproduce these degrees and the
displayed leading coefficient on three full univariate rays. They also
compare 123 independent formal-radical products to the scalar circuit,
verify all four actual coefficient payloads, and perform three additional
degree rays using the actual complete coefficient tuple modulo the primes.
These checks support the formulas; the proof above supplies the
unbounded theorem and generic exact degree.

## Comparison and novelty boundary

Source 34's lowest-degree twelve-positive product has degree 1022 and
124 operations; its corresponding system has degree 1013 and 120
operations. The present product has degree 938 and 122 operations, and
its system degree 929 and 117 operations. Thus both coordinates improve
on those lowest-degree source-34 presentations. Source 31's degree-1081
product at 108 operations and shifted system at 102 operations retain
their better operation counts. There is no claim here of eleven
positive variables, fewer than nine natural variables, or a global
minimum. The new mathematical step is the low-degree separator obtained
from authentic inequalities, combined with existing carrier translations
and the existing complete shift in w.

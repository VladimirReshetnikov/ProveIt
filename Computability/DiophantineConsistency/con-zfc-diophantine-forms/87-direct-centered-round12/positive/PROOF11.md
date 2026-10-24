# Two centered gaps and a cofinal auxiliary orbit

## Result and precise boundary

The literal polynomial `p11_degree211.json` has eleven strictly positive integer unknowns, exact degree 211, and 113 live binary arithmetic operations (64 multiplications, 32 additions, 17 subtractions). The incoming Joint_Guards endpoint has degree257/114 operations; round11 has degree277/111. This construction improves the former in both metrics. It inherits the complete compact44 fixed tuple and the source70 weighted positive-source interface, with its native compiler and K215 calibration. It is an ordinary proof formalizable in ZFC, not a new Lean/Rocq certificate or global minimality claim. Centering is prior art in Joint_Guards; the changes here are simultaneous centering of both large roots, early divisibility followed by a cofinal auxiliary shift, and a degree-two gap bound.

## Literal definition

The positive unknowns are j,F,alpha,i,T,X,Y,n,eta,zeta,gamma. Fixed numerals are beta,K0,MC,MF with MF already shifted, bound by native/ACTIVE_BINDING.json. Set

J=3j+1, q=beta J+1, C=q-F-alpha, E=XY,
k=eta+zeta, c=kY+eta, a=E+Y, Aparam=a+2,
H=4a+3, Delta=a^2+H=Aparam^2-1, ell=E kY,
R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
M=q^3(q-1), Bt=(qK0+X)C-qF, Dtau=ell(ell+k)+1,
I=i c^2, Df=1+Delta I^2, Q=Delta(Df-1), delta=Q-1.

The new registers are

Told=T+q+alpha, b=c Told-R, V=Df b-c,
Dcenter=Aparam I, L=k Told+F, W=1+(q-1)L,
Zbar=M(ell+k+n+L+V+Dcenter)+(q-1)Y-q^3 W Bt.

Keep the adaptive carrier and norm:

r0=k-R-1, S=4qY, U=qS,
Dstar=U(X+ac)+H(U gamma+SX-r0),
A1=Dstar^2-U^2(1+Delta c^2),
A=M^2 Dtau, Bf=M^2 Df, Cnum=M^2(QV^2-1),
Tn=delta^2 A Bf, Rn=delta Cnum,
Jn=delta(Zbar^2-A-Bf)-Cnum,
Ncenter=Jn^2-4[Tn+Rn(A+Bf)],
N8=Ncenter^2-64 Tn Rn Zbar^2,
P11=N8+A1+N8 A1.

All registers are abbreviations, not quantified variables. The JSON is a literal division-free circuit. The proof-only rational number Dy=(QV^2-1)/(Q-1) is not a circuit division.

## Radical recovery before positivity

The source70 separation proof is unconditional in the integral value b: I>=c^2, c>=3, a>=2 imply 1<Dtau<Df<Q and |V|>1. Let tau=sqrt(Dtau), f=sqrt(Df), y=sqrt(Dy). If b=0, V=-c and f>tau+y; otherwise y>f+tau. Dtau,Df,Dy are pairwise distinct: Dtau<Df<Q, and an equality Dy=D in {Dtau,Df} would imply Q(D-V^2)=D-1 with 0<D-1<Q. Consequently no signed sum vanishes.

The three-root norm identity implies N8=0 gives Zbar/M=tau_*+f_*+y_* with the corresponding signed roots. They are rational: for signed roots x1,x2,x3 with distinct squares a1,a2,a3 and nonzero rational sum s, put u=(s^2-a1-a2-a3)/2 and v=(u^2-a1a2-a1a3-a2a3)/(2s). Then xi=ai(ai+u)/(ai s+v); the denominator is xi(xi+xj)(xi+xk), nonzero by distinctness. The first two roots are integral because their squares are integral. The third is integral by adjacent-Pell rational saturation: QV^2-(Q-1)y_*^2=1 with Q,V integral implies y_* integral. A full descent proof is recorded below.

Therefore M divides Zbar. Reduction modulo q^3 gives q^3|Y. This argument uses neither C>0, nor V>0, nor a recovered positive transport gap.

## Small bounds after early divisibility

Write m=(MC+qMF)J. The authentic masks give 0<m<2q^2 and q>=16. Since F>0,

R < q(q-1)(q^2-1)+alpha(q^2-1)+2q^2 < q^3(q+alpha).

For the second strict inequality, the difference is
q^3-q^2-q+alpha(q^3-q^2+1)>0.
Also R> -F q^3, since only the term -(q-1)F(q^2-1) can be negative in the displayed definition of R. As q^3|Y, Y>=q^3 and c>Y. Hence

c(q+alpha)>R, b=c Told-R>cT>=c, V=Df b-c>1.

Now Df>Delta+1 (I>1), so delta=Delta(Df-1)-1>(Delta-1)Df. Since c=kY+eta<k(Y+1)<=2kY and Delta-1=(a+2)^2-2>4Y^2,

0<y-V=(V^2-1)/(delta(y+V))<V/delta<b/(Delta-1)
 <c Told/(Delta-1)+F q^3/(Delta-1)<k Told+F=L.

This is the essential cheap gap bound. L>k. Independently, Dcenter^2-Df=I^2-1>0, so 0<f<Dcenter and 0<Dcenter-f=(I^2-1)/(Dcenter+f)<I.

## Soundness

Set f_old=|f_*|, y_old=|y_*|, u=y_old-V>0, i_old=i, and

r=n+L+V+Dcenter-f_*-y_*.

The preceding bounds imply r>=n+L-(y-V)+Dcenter-f>0, with no assumption on the recovered signs. The first weighted carrier with this r and weight hstar=L is M tau_*. The normalized strong equation and auxiliary equation hold, as does A1=0. The weighted source theorem therefore reconstructs a positive native source solution and a finite ZFC refutation. The signs inside r must not be replaced by absolute values; they are bounded by absolute values only in the positivity proof.

N8 is a square modulo4, as is A1 because4|U. Thus P11=0 forces N8=A1=0: the factors (1+N8),(1+A1) have product1, and the possibility that both are-1 would require residual-2 modulo4. Conversely simultaneous zeros give P11=0.

## Cofinal positive auxiliary reconstruction and completeness

Canonical native witnesses supply the fixed outer coordinates and any normalized strong Pell pair f,I with c^2|I. Source61's positive auxiliary reconstruction supplies one positive pair V0,y0 with

QV0^2-(Q-1)y0^2=1, V0=f^2(c T0-R)-c.

Let B=[[2Q-1,2(Q-1)],[2Q,2Q-1]]. It has determinant1, preserves this norm, and has positive entries. Put h=c f^2. Its residue lies in the finite group SL_2(Z/hZ), so B^e is the identity modulo h for some e>0. Iterating B^e gives positive pairs (Vj,yj), strictly increasing and unbounded, with Vj=V0 modulo h. Thus

Tj=(Vj+c+R f^2)/(c f^2)

is integral, unbounded and eventually positive. Take j large enough that Tj>q+alpha and k Tj+F>I. Set Told=Tj, T=Tj-q-alpha>0, L=k Told+F>I, and u=yj-Vj>0. This proves the needed cofinality rather than assuming it of the inherited lemma.

Compute W only after this choice. The canonical transport quotient t0=Bt/(q-1)>=q and s=Y/q^3<k give

r=Wt0+tau-ell-k-s>qW-2k>2L>L+I.

The penultimate inequality follows from q>=16 and L>=k. Define

n=r-L-V-Dcenter+f+y=r-L-(Dcenter-f)+u>0.

Then Zbar=M(tau+f+y), so N8=0. The canonical adaptive carrier supplies positive gamma with A1=0, unchanged from source70. This gives a positive zero of P11 from every finite refutation. Hence, in ZFC, lack of positive zeros is equivalent to Con(ZFC), with exactly the inherited named compiler/calibration boundary.

## Adjacent-Pell rational saturation, full descent

If Q>1,V integral,y rational satisfy QV^2-(Q-1)y^2=1, take signs positive. Write y=a/m in lowest terms. Then m^2|Q-1, hence (Q-1)y is integral. If V=1 then y=1. Otherwise put V'=(2Q-1)V-2(Q-1)y and y'=(2Q-1)y-2QV. V' is integral, nonzero, and the same norm equation holds. From y>V and QV>(Q-1)y one gets -V<V'<V. Also y' has the same reduced denominator m because 2Q-1=1 modulo m. Induction on positive |V| reaches V=1, forcing m=1.

## Exact degree on the actual coefficient slice

Let z=Zbar-M(V+Dcenter), e=I^2-1, D=Dcenter, and H0=z^2+2MDz+M^2e-A. Then

Jn=delta[H0+2MV(z+MD)]-M^2(V^2-1).

Using Bf=M^2(D^2-e) cancels the apparent degree102 part of Ncenter. Its degree99 leading form is 8Q0^2 M0^3 V0^2 D0 z0. The degree198 leading form of N8 is

64 Q0^4 M0^6 V0^4 D0^2 (z0^2-M0^2 Dtau0).

Here q0=3 beta j, k0=eta+zeta, R0=q0^3(q0-F),
Bt0=(K0q0+X)(q0-F-alpha)-q0F,
Q0=i^2 k0^4 X^4Y^8, Df0=i^2k0^4X^2Y^6,
V0=-Df0 R0, D0=i k0^2XY^3, L0=k0(T+q0+alpha),
ell0=k0XY^2, M0=q0^4, z0=M0(ell0-L0 Bt0).

Thus z0^2-M0^2 Dtau0=M0^2 L0 Bt0(L0 Bt0-2ell0), not zero. The exact degree13 carrier head is

32q0^2k0X^2Y^4[4q0^2Y gamma+q0^3(q0-F)].

In P11, the coefficient of j^48 i^18 eta^39 X^30 Y^67 F^4 T^2 alpha^2 gamma is exactly 8192(3 beta)^48>0. To see this, choose the gamma term, then T^2 in the first summand of L0 Bt0(L0 Bt0-2ell0), then the minimum q0 degree, and finally alpha^2 in Bt0^2 and F^4 in(q0-F)^4. This coefficient is independent of K0,MC,MF, establishing exact degree211 for the authentic tuple. The accompanying tests check literal transcription and exact algebra, not the unbounded semantic interface.

# A compact separating weight for the twelve-positive-variable norm

## Scope

This is an algebraic replacement for the weight and first-root coefficient
in package 21-norm12. It uses the entire coefficient tuple from a proved
blank-machine compiler, with beta=B-1 and shifted MF. The coefficient
adapter and the inherited K215 logical endpoint are separate dependencies.
The proof below concerns strictly positive supplied coordinates only; it
must not be interpreted as a proof of the 26-unrestricted-integer lift.

The supplied coordinates are J,F,alpha,z,h,i,T,s,w,eta,zeta,r > 0.
Use the original definitions

    q=beta J+1, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3,
    Delta=a^2+H=(a+2)^2-1,
    ell=E*kY, A=1+ell(ell+k), G=1+Delta*c^2,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    Nk=k-hE-R, Cw=q-F-alpha,
    Nt=(K0+w)Cw+q-F-z(q-1).

Set

    I=i c^2, I2=I^2, D=1+Delta I2, Q=Delta^2 I2, d=Q-1,
    v=cT, b=c+RD, e=Q(D v^2+b^2)-1, Baux=2Qvb.

The new expressions are

    W=T^2+X I2, L=1+HW, Jtau=4HW, S=X+ac+Hr.

Use formal roots u,tau only to define a finite polynomial norm:

    N = Norm_(u^2=G) Norm_(tau^2=A)
          ([d(S-Lu-Jtau*tau)^2-H^2 e]^2-H^4 Baux^2 D).

The finite norms introduce no supplied variables. They are expanded by the
included division-free binary arithmetic circuit. The three equations are
Nk=1, Nt=1, N=0. The single product polynomial is

    P=Nk Nt(1+N)-1.

## 1. Bounds available before restoring roots

The inherited weak transport bootstrap, applicable with Nk=Nt=epsilon
in {+1,-1}, gives Cw>=0, q>=16, 0<R<q^4-2, and E>=q^4>R+2.
As h>0,

    k=R+hE+epsilon >= R+E-1 > 2R.

Also X>=16, Y>=4096, a=Y(X+1), c>1, I=i c^2>c, and Q>1.
These inequalities require no norm-root recovery.

In a normal splitting field, N=0 supplies one coherent choice of roots
u^2=G, tau^2=A, f^2=D and y with

    d y^2=Q(vf-b)^2-1,
    S=L u+Jtau*tau+H y.

The first statement follows by successively factoring the displayed norm;
there is no assumption that independently chosen signs are compatible.
For every embedding, f is sent to +sqrt(D) or -sqrt(D). Consequently

    |y'| < sqrt(Q/(Q-1)) (v sqrt(D)+b).

This inequality includes potentially non-real y'. Indeed y'^2 is real,
and its absolute value is bounded by the larger of
|Q(v sqrt(D)-b)^2-1| and Q(v sqrt(D)+b)^2-1. The latter is the larger
because it is positive and greater than one.

## 2. A short bound for every conjugate of y

Since I>c,

    D/G=(1+Delta I^2)/(1+Delta c^2) < I^2/c^2.

Also sqrt(D)<(a+2)I and sqrt(G)>ac. Therefore

    v sqrt(D)/sqrt(G)<TI,
    c/sqrt(G)<1/a,
    D/sqrt(G)<(a+2)I^2/c.

Using sqrt(Q/(Q-1))<3/2 and R/k<1/2, c>kY gives

    |y'|/sqrt(G)
      < (3/2)TI + 3/(2a) + (3/2)R(a+2)I^2/c
      < (3/2)TI + 3/(2a) + (3/4)(X+2)I^2.

The last inequality uses (a+2)/Y=X+1+2/Y<X+2.
The elementary square inequality (T-3I/4)^2>=0 gives

    (3/2)TI <= T^2+(9/16)I^2.

As 3/(2a)<I^2 and X>=16,

    |y'|/sqrt(G)
      < T^2 + ((3/4)X+49/16) I^2
      < T^2+X I^2 = W.

Thus every conjugate satisfies |y'|<W sqrt(G). This is a strict uniform
bound before u, tau or f has been shown rational or integral.

## 3. A short comparison of the first and main radicals

From sqrt(G)<(a+2)c, sqrt(A)>ell=kXY^2, c<k(Y+1),
and a+2=Y(X+1)+2<Y(X+2),

    sqrt(G)/sqrt(A)
      < ((X+2)/X)((Y+1)/Y)
      <= (9/8)(17/16)=153/128 < 4/3.

Here the deliberately weak Y>=16 is enough. Since HW>1,

    Jtau sqrt(A)=4HW sqrt(A)
      >3HW sqrt(G)
      >(1+2HW)sqrt(G)
      =(L+HW)sqrt(G).

Also L sqrt(G)>HW sqrt(G)>H|y'|.

## 4. Recovery of rational roots

Suppose tau is irrational. Some automorphism of a finite normal splitting
field sends tau to -tau. Subtracting its image of
S=L u+Jtau*tau+H y from the original relation gives

    2 Jtau sqrt(A) <= 2 L sqrt(G)+2HW sqrt(G),

contradicting Section 3. Therefore tau is rational, hence integral because
it is a square root of an integer.

Now if u were irrational, an automorphism sends u to -u while fixing tau,
which is rational. The same subtraction gives

    2 L sqrt(G) <= 2H W sqrt(G),

again impossible. Hence u is integral. The linear relation makes y rational.
Since Baux>0, f=(e-d y^2)/Baux is rational and therefore integral.

The specialized Pell saturation lemma from package 21 applies to

    Q(vf-b)^2-(Q-1)y^2=1,

because Q=(Delta I)^2 is the square of an integer at least two and vf-b
is integral. It proves y is integral. This step is essential; merely
clearing H from the linear relation would not establish integrality.

## 5. Restoring the main congruence and logical soundness

Since L=1 mod H and Jtau=0 mod H, the integral linear relation gives
u=X+ac mod H. Thus gamma=(u-X-ac)/H is integral. The recovered integers
satisfy exactly the signed normalized Pell interface of package 21,
including its ordinary conversion i_ordinary=Delta*i. The inherited
weak-sign compiler theorem forces Nk=Nt=1 and recovers a blank K215 halt.

Conversely, given a canonical positive normalized compiler witness, let
u=X+ac+H gamma and take positive tau,y. Define

    r=gamma+W*u+4W*tau+y.

This is a positive integer and it makes
S=L u+4HW*tau+H y. The coherent factor in the norm vanishes. Hence N=0
and Nk=Nt=1. This proves exact existential equivalence.

The original parity argument is unaffected by changing the scalar
coefficient of tau. The odd coefficient N1 in the outer quadratic norm
N=N0^2-G N1^2 is divisible by 8. Thus N=N0^2 mod64 and 1+N cannot be -1.
A zero of P=Nk Nt(1+N)-1 therefore yields N=0 and equal unit signs for
Nk,Nt, exactly the weak-sign situation already proved sound.
The sum of squares (Nk-1)^2+(Nt-1)^2+N^2 gives a conservative alternative.

## 6. Literal costs and a uniform exact-degree proof

The five-gate strong block is written as

    I=i*c2; I2=I*I; Dm1=Delta*I2; D=Dm1+1; Q=Delta*Dm1.

It replaces the original five-gate block without increasing its cost, and
makes I2 available for W. T2=T*T and v2=c2*T2 replace the two gates
v=c*T and v2=v*v; the original circuit uses v only through v2. Thus T2
is available for free, and W takes two further gates, XI2=X*I2 and
W=T2+XI2, instead of the old three-gate weight. The reduced tau coefficient
costs one extra gate because its square replaces H^2 L^2. The two changes
cancel, so every presentation retains the old operation count.

The circuit ledgers are:

| Presentation | Multiplications | Add/subtract | Total | Exact degree |
|---|---:|---:|---:|---:|
| Three-equation system | 72 | 40 | 112 | max 1072 |
| Product | 74 | 42 | 116 | 1081 |
| Sum of squares | 75 | 44 | 119 | 2144 |

The core degrees are

    deg(c)=5, deg(a)=deg(H)=6, deg(Delta)=12,
    deg(I)=11, deg(I2)=22, deg(D)=34, deg(Q)=deg(d)=46,
    deg(b)=38, deg(e)=122, deg(W)=24, deg(L)=deg(Jtau)=30.

In the pair-ring circuit a0=Jtau^2 A and V0=S^2+L^2 G have degree82;
V1=2SL has degree41. Consequently C0=d(V0+a0)-H^2 e has degree134,
with unique leading term -H_top^2 e_top, while C1 has degree87.
The even outer coefficient N0 has degree536 with leading term C0_top^4,
whereas the odd coefficient N1 has degree at most489. Thus N0^2 has
exact degree1072 and G N1^2 has degree at most1000. No highest-degree
cancellation is possible.

Set q0=beta J and k0=eta+zeta. The explicit leading form is

    N_top=2^32 i^48 k0^96 w^80 s^176 q0^656 (q0-F)^16.

It is nonzero for every fixed beta>0. The two outer leading forms are
Nk_top=-hws q0^4 and Nt_top=w(q0-F-alpha)-zq0, so the product has exact
degree1072+7+2=1081. The sum of squares has degree2144 because N^2 is its
unique highest-degree summand.

The supplied builder checks every supplied variable and fixed port is
live, counts all binary additions/subtractions/multiplications, and checks
24 signed fixtures against an independently implemented eight-dimensional
conjugate-product evaluator. The finite checks supplement the uniform
proof; they do not construct an accepting K215 run or certify the inherited
compiler in a proof assistant.

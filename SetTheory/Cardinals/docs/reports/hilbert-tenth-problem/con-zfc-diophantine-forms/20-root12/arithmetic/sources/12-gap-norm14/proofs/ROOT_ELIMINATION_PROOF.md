# Fourteen positive unknowns by eliminating the strong Pell root

Keep the blank-input definitions q,C,X,Y,E,k,c,a,H,Delta,Dmain,R,L and the
four factors N0,N1,Nk,Nt from ORDINARY_BLANK_PROOF.md, with its old transport
coordinate z_old. Remove the variable f. The remaining fourteen positive
coordinates are

    J,F,alpha,z_old,h,i,T,s,w,tau,eta,zeta,y,gamma.

Here i has the **normalized** meaning, as in package 06's P67, not the
ordinary meaning in P69. The constant ports are unchanged.

Define integer polynomial abbreviations

    Q=(Delta i c^2)^2,
    Dstar=1+Delta i^2 c^4,
    b=c+R Dstar, v=cT,
    Astar=Q(Dstar v^2+b^2-y^2)+y^2-1,
    Bstar=2Qvb,
    Kstar=Astar^2-Dstar Bstar^2,
    P4=N0 N1 Nk Nt.

Two single equations are

    Phi14=P4(1+Kstar)-1=0,                          (1)

and

    AO=P4[Q(Dstar v^2+b^2)+(1-Q)y^2]-1,
    BO=P4 Bstar,
    Psi14=AO^2-Dstar BO^2=0.                       (2)

The emitted circuits avoid explicitly constructing Bstar and BO:
Dstar Bstar^2=4(Q Dstar v^2)(Q b^2), and similarly with P4 inserted.
This is the norm-elimination idea of packages 03/05 with the blank-input
loader of 06; the old fixed marker and its residual square disappear.

## 1. Fourteen-positive-variable soundness

For (1), every displayed integer factor is a unit. Since Bstar is even,
1+Kstar=1+Astar^2 modulo 4 cannot be -1. Hence Kstar=0 and P4=1.
The four factors inside P4 are therefore units. The usual negative-Pell
descent and modulo-four argument give N0=N1=1. The transport-unit bound
gives C>=0 and all the blank packing estimates, in particular R>0.
Thus b,v,Q are positive and Bstar is nonzero. The rational number

    f=Astar/Bstar

satisfies f^2=Dstar. A rational square root of an integer is an integer:
write the fraction in lowest terms and compare prime valuations of its
square. Since Dstar>1, f is a nonzero integer. Its sign is immaterial.

With V=vf-b one has the exact remainder identity

    Astar-Bstar f=Q(V^2-y^2)+y^2-1.                (3)

It vanishes by the definition of f. Also

    f^2-Delta i^2c^4=1,
    V=c(Tf-1)-Rf^2.

Consequently we have restored a signed-f normalized blank solution. Put
i_ordinary=Delta i; its strong equation becomes the ordinary strong
equation, with the same Q auxiliary coefficient. The signed-domain proof
in ORDINARY_BLANK_PROOF.md now gives a genuine K215 blank halting run.
There is no need to prove a separate sign theorem for the reconstructed
f or to replace T by its negative.

For (2), reduction modulo P4 gives Psi14=1 modulo P4, so a zero has
P4=+1 or -1 (P4=0 directly gives Psi14=1). Thus each of N0,N1,Nk,Nt is
a unit and the same outer bounds imply R>0. Set f=AO/BO, which is again
well-defined and integral because f^2=Dstar. The exact identity is

    AO-BO f=P4[Q(V^2-y^2)+y^2]-1.                 (4)

Therefore the full normalized product equation is restored. Conversion
to the ordinary strong coordinate and the same signed-domain theorem
prove soundness. This argument does not presume the sign of P4.

## 2. Completeness

Start with a canonical positive blank compiler solution of package 06.
Its normalized strong equation gives f^2=Dstar and the auxiliary equation
gives Astar=Bstar f. Its four remaining factors all equal 1. Thus both
(1) and (2) vanish after f is deleted. The same fixed coefficients encode
exactly the same halting predicate. In combination with the K215
calibration, ZFC proves that either displayed equation has no positive
integer solution if and only if Con(ZFC).

## 3. An expanded signed domain and thirty-two integer unknowns

As with the ordinary construction, the nine coordinates

    J,F,alpha,z_old,i,s,w,eta,zeta

must be positive, while

    h,T,tau,y,gamma

may be arbitrary integers. The only new issue is possible T=0, which
would make the root-reconstruction denominator vanish.

For either equation, the preceding unit argument establishes the outer
bounds before root reconstruction. These imply 0<R<a<Delta and c>2.
Moreover

    Q=Delta(Dstar-1),
    Q-b=(Delta-R)Dstar-Delta-c
        >=Dstar-Delta-c
        =1+Delta(i^2c^4-1)-c>0.                    (5)

Thus 2<b<Q. If T=0 then v=0 and Bstar=0. For (1), Kstar=0 gives
Astar=0, hence

    Q b^2-(Q-1)y^2=1.                             (6)

For (2), AO=0 gives P4[Q b^2-(Q-1)y^2]=1. The bracket cannot be -1
modulo 4 because Q is a square, so again (6) holds.

Every integral solution of (6) with b>1 satisfies b>=2Q-1. Indeed its
rearrangement b^2-1=(Q-1)(y^2-b^2) implies |y|>=b+1; if 1<b<=2Q-2,
then b^2-1<(Q-1)(2b+1), a contradiction. This conflicts with b<Q.
Therefore T is nonzero on every zero, so Bstar and BO are nonzero.
All root-reconstruction steps remain valid with signed T, and the
ordinary signed-domain proof applies after i_ordinary=Delta i.

Replace the nine positive coordinates by independent copies of
1+u^2+v^2+t(t+1), leaving the five signed coordinates untouched. The
result is one polynomial in 9*3+5=32 unrestricted integer variables.
Its zero existence is equivalent to K215 blank halting.

## 4. Literal counts and uniform exact degrees

`blank14_norm75.json` has 75 operations, 44 multiplications and 31
additions/subtractions. `blank14_outer73.json` has 73 operations,
44 multiplications and 29 additions/subtractions. Every gate and
supplied port is live. All fixed-coefficient multiplications are charged.

Put Q0=beta J, k0=eta+zeta and

    T2=w(Q0-F-alpha)-z_old Q0.

The norm polynomial's leading homogeneous form is

    8 h gamma i^12 k0^27 w^21 s^48
      Q0^177 (Q0-F)^4 T2,                         (7)

of degree 293. For example its coefficient at

    J^182 h gamma i^12 eta^27 w^21 s^48 z_old

is -8 beta^182, nonzero for every authentic compiler.

For verification, Q has degree 46, Dstar degree 34, b degree 38 and
v degree 6. The unique highest term of Astar is Qb^2, of degree 122.
Hence Kstar has degree 244, since its other summand Dstar Bstar^2 has
degree 214. P4 has degree 49, giving degree 293.

The outer polynomial's leading form is

    64 h^2 gamma^2 i^12 k0^30 w^26 s^56
       Q0^206 (Q0-F)^4 T2^2,                     (8)

of degree 342. Its coefficient at

    J^212 h^2 gamma^2 i^12 eta^30 w^26 s^56 z_old^2

is 64 beta^212. Its squared leading term has degree 342 while the
subtracted cross-term has degree 312, so cancellation is impossible.

For the 32-integer-variable versions, the nine positivity substitutions
add 63 arithmetic gates. Their exact counts/degrees are therefore

    norm: 138 operations, degree 584;
    outer: 136 operations, degree 680.

These degree claims use weight two for guarded coordinates and weight
one for signed coordinates. The top terms (7) and (8) have signed
weights 2 and 4 respectively, so their new degrees are 2*293-2 and
2*342-4. Direct weighted upper bounds give the same values; the
disjoint positive substitutions preserve nonvanishing.

## 5. Reproduction and scope

Run `python3 build_fourteen.py`. The emitter reads only the exact baseline
JSON and its own algebraic helper. It verifies counts, operand binding and
liveness, checks 100 signed/rational full-formula cases, 100 exact root
remainder identities, 64 integer-substitution cases, and two modular
univariate degree calculations for each output. The mathematical root
reconstruction, signed-domain theorem and inherited compiler are separate
proof obligations; finite arithmetic tests do not establish them.

These fourteen-variable and thirty-two-integer-variable equations improve
the explicit family under review. They are not global variable minima;
classical universal representations use fewer unknowns at quite different
degrees and coefficient-description costs.


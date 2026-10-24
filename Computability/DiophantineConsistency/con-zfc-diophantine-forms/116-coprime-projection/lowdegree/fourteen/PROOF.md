# Double-centered two-root carrier: fourteen integers, degree 108

## Result

This sibling removes f from the fifteen-integer equation in the parent directory. Its literal polynomial has fourteen unrestricted integer unknowns, exact degree 108, and 119 live binary arithmetic operations (69 multiplications, 30 additions, 20 subtractions). Integer-zero existence is equivalent to the adjacent fifteen-integer equation and hence to its pinned normalized seventeen-integer source. All inherited compiler/refutation and formalization boundaries remain exactly as stated in `../PROOF.md`.

The ordinary novelty is a double-centered two-root resultant. It uses the existing first-root carrier to enforce the scale and quadratic main projection while recovering both first and strong Pell roots. Monic-quartic integrality extracts the scale before either radical is classified, excluding v=0 without an exceptional-branch assumption. There is no hidden witness or rational-domain convention.

## 1. Complete formula

Keep every polynomial abbreviation of the fifteen-integer equation except that f is no longer a variable and the strong row is removed. The fourteen variables are

    j,C,z,h,r,v,w,T,c,n,y,p1,p2,p3.

Replace its three f-dependent abbreviations by

    Df=1+Delta I^2,
    Q=Delta(Df-1)=Delta^2 I^2,
    V=Df(cT-R)-c.

Keep M,U,Klo,Z,L,budget,pos unchanged. Define

    A=2L+k, B=2(a+2)I,
    aa=4-k^2, bb=4(1-I^2),
    D0=Z^2+2BUZ+U^2(aa-bb),
    E0=Z+U(A+B),
    B0=A[Z^2+2BUZ-bb U^2]-aa U[Z+UB],
    N=D0^2+4U E0 B0.

The defining equation is

    P14=N^2+[V^2-(Q-1)y(2V+y)-1]^2+[budget-pos]^2=0.

The runtime DAG evaluates the identical norm more cheaply as

    E0=Z+U(A+B),
    N=[E0^2-4U^2(Dtau+Df)]^2-64U^4 Dtau Df,

while the D0,B0 expression above exposes its degree cancellations. The prior centered evaluator is retained as `centered_equation.json` for comparison. `specification.json` records the complete ordered runtime abbreviation list; `equation.json` is the complete division-free DAG. Capital A and B here are only local root centers, not the fixed cone coefficients.

## 2. Exact norm identity, with no divisions in the polynomial

For formal indeterminates t,A,B,aa,bb, put

    D=t^2+2Bt+aa-bb.

The exact polynomial identity is

    D^2+4(t+A+B)[A(t^2+2Bt-bb)-aa(t+B)]
      =[(t+A+B)^2-(A^2+aa)-(B^2+bb)]^2
         -4(A^2+aa)(B^2+bb).

The right side is the product of the four linear factors

    t+A+B +/- sqrt(A^2+aa) +/- sqrt(B^2+bb).

As already proved in the fifteen-integer reduction, U is unconditionally nonzero. Substituting t=Z/U and multiplying by U^4 gives exactly N, with every denominator cleared. Also, identically,

    A^2+aa=4[1+L(L+k)]=4Dtau,
    B^2+bb=4[1+Delta I^2]=4Df.

Here Dtau=1+ell(ell+1)k^2 with ell=XY^2, so Dtau>=1 for integer inputs. The radicands in this identity are integers. At a zero, the rational number

    x=Z/U+A+B

is a root of the monic integer polynomial

    x^4-2(4Dtau+4Df)x^2+(4Dtau-4Df)^2.

The rational-root theorem therefore proves x is an integer, before any radical extraction or guard estimate. Since A+B is an integer, Z/U is an integer. The unconditional coprime CRT proof from the fifteen-variable equation immediately gives

    v=q^2(2v0+1),    H|Klo.

Thus v is nonzero and the full cubic scale is already licensed. The v=0 branch is excluded by monicity and CRT, without dividing by a radical sum or presupposing positive roots.

## 3. Root extraction after the licensed scale

The unchanged guard gives budget=pos>0. Consequently k is nonzero and

    |eta/k|<1/2,    |c|>|k|(|Y|-1/2).

Put x0=|X|>=64, m=|Y|>=16, K=|k|>=1. In fact the recovered cubic scale gives m>=4096, but the weaker bound16 suffices. We have

    sqrt(Delta) > (x0-1)m-3 > x0*m/2,
    |c| > K(m-1/2) > 3Km/4.

In particular Delta>=3 and both positive real roots tau=sqrt(Dtau), f=sqrt(Df) exist. Since I=(2r+1)c^2 and |2r+1|>=1,

    f > sqrt(Delta)c^2 > (9/32)x0*m^3*K^2.

Also |ell|=x0*m^2 and ell(ell+1)>=0 give

    tau <= K sqrt(ell(ell+1)+1)
         < K(x0*m^2+1) < (9/8)K*x0*m^2.

Therefore f/tau>mK/4>=4. In particular no signed sum epsilon1*tau+epsilon2*f is zero.

The exact norm factorization now gives, for some independent signs,

    Z/U+A+B = epsilon1*2tau + epsilon2*2f.

The rational signed sum s=epsilon1*tau+epsilon2*f is nonzero. Squaring and rearranging yields

    tau=(s^2+Dtau-Df)/(2 epsilon1 s),

so tau is rational, and then f is rational. A rational number whose square is an integer is integral. Thus both roots are integers. The proof never uses root rationality to license the scale: monic-quartic integrality already did so in Section2.

## 4. Two-way maps to the fifteen-integer equation

### Fourteen to fifteen

Keep every shared variable except replace the carrier coordinate n. Let tau,f be the positive integer roots just proved. The CRT gives integer offsets

    g=Klo/H, v0=(v-q^2)/M.

Set

    f15=f, n15=tau-L-g-v0.

Then the fifteen-integer carrier satisfies Z15/U=tau-L, and its first row vanishes because tau^2=1+L(L+k). Its strong row vanishes because f15^2=Df. Its auxiliary and budget rows are unchanged. This is an actual fifteen-variable integer zero. No main-root classification is repeated here; the already-proved fifteen-variable theorem handles it after this restoration.

### Fifteen to fourteen

At a fifteen-variable zero its carrier yields the integer first root t+L; choose tau=|t+L|. The strong row yields f=|f15|. Both are positive integers, the CRT gives g and v0 above, and all f-dependent quantities use only f15^2. Set

    n14=2tau+2f-A-B-g-v0.

Then Z14/U+A+B=2tau+2f, so one of the exact norm factors is zero. Its auxiliary and budget rows coincide with those of the old zero. Thus all three squared rows vanish.

These maps apply to every zero in either direction. They preserve all shared coordinates other than n, restore the omitted f when needed, and introduce no integrality, parity, canonical-choice, or existence assumption not proved above.

## 5. Exact degree and arithmetic count

The unchanged outer degrees are those in the fifteen-variable proof. Now

    deg(Df)=14, deg(Q)=22, deg(V)=19,
    deg(A)=11, deg(B)=7, deg(aa)=10, deg(bb)=6,
    deg(D0)<=22, deg(E0)<=17, deg(B0)<=31.

Hence deg(N)<=54, the auxiliary row has degree at most42, and the guard row at most16. The complete polynomial has degree at most108.

Write q0=6 beta j, X0=12q0 w, Y0=q0 v, a0=X0Y0, U0=8q0^2 X0Y0, I0=2rc^2 and k0=R0+hX0Y0. The unique degree54 leading contribution is

    N54=8U0^4 A0^2 B0 n
       =64U0^4 L0^2 a0 I0 n,
    A0=2L0, B0=2a0I0, L0=X0Y0^2 k0.

Selecting h^4 in N54^2 yields the actual coefficient

    [j^56 w^18 v^22 h^4 r^2 c^4 n^2] P14
      =2^130 3^74 beta^56 > 0.

The exponents sum to108, and the other two squared rows have smaller degree. This proves the exact degree over the authentic fixed coefficients. The name B0 used for the scaled resultant register in the literal formula should not be confused with B0 as a leading part in the final two displayed identities; the latter is explicitly 2a0I0.

The optimized direct-norm DAG uses119 live gates:69 multiplications,30 additions,20 subtractions. Fixed literals and coefficient leaves are not hidden arithmetic gates, and every one of the fourteen input coordinates is live. The independent review checks the full norm identity, all register cuts, exact leading forms, constants, liveness, and bad mutations. These checks certify finite algebra and transcription, not a new native compiler theorem or Con(ZFC) itself.

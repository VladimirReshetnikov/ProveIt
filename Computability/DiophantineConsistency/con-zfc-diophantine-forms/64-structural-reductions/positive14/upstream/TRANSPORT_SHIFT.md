# A compact separation weight for twelve positive unknowns

Source baseline: ProveIt package `21-norm12`, read at commit
`ae3007ca4467011e0e051c84acb4a1dd13971b0e`. The proposed coefficient binding
is the entire `wang943-compact-5pow10` tuple of package `19-wang943`, whose
whole-tuple transfer theorem preserves the blank normalized interface.
Its exact base is B=2^(5^10), and its four ports are beta=B-1, K0=K,
MC, and MF=MF_source=MF_native+B-1. No port may be mixed with another
recipe. The coefficient proof is `compiler/WANG943_COEFFICIENTS.md`
together with `compiler/WANG943_COMPACT_LAYOUT.md` in package19.

The new result is an ordinary mathematical reduction, not a new
Lean/Rocq theorem. The complete compiler and K215/refutation endpoint
remain inherited dependencies. The new weight and the final degree/gate
improvements are proved here.

## 1. Definitions and outputs

All twelve supplied coordinates are strictly positive integers:

    J,F,alpha,z,h,i,T,s,w,eta,zeta,r.

Fixed coefficient ports are beta=B-1,K0,MC,MF. Set

    q=beta*J+1, Cw=q-F-alpha,
    X=w*q, Y=s*q^3, E=X*Y,
    k=eta+zeta, c=k*Y+eta,
    a=E+Y, H=4*a+3, Delta=a^2+H,
    ell=E*k*Y, A=1+ell*(ell+k), G=1+Delta*c^2,
    R=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J,
    Nk=k-h*E-R,
    Nt=(K0+w)*Cw+q-F-z*(q-1),
    I=i*c^2, D=1+Delta*I^2,
    Q=(Delta*I)^2, d=Q-1,
    v=c*T, b=c+R*D,
    e=Q*(D*v^2+b^2)-1, Baux=2*Q*v*b.

The new separation weight is

    W=I*(T+k*I), L=1+H*W, S=X+a*c+H*r.

Define the finite norm polynomial

    N = product over u=+-sqrt(G), tau=+-sqrt(A), f=+-sqrt(D)
        [d*(S-L*u-H*L*tau)^2-H^2*e+H^2*Baux*f].

This product is invariant under the three formal sign changes and is an
integer polynomial, even when the radicands specialize to dependent
squares. It is evaluated by the explicit division-free circuit in
`compact_norm12_product.json`. It introduces no quantified roots.

The single equation is

    P=Nk*Nt*(1+N)-1=0.

The unshifted three-equation system is Nk=1,Nt=1,N=0. Its most direct
comparison implementation omits the final norm subtraction, giving 111
operations. Shift the transport coordinate by z_old=z+1 to obtain the
110-operation system

    Nk=1, (K0+w)*Cw=F+z*(q-1), N=0.

The norm does not depend on z. The shifted system's sum of squares has
118 operations and degree 2208. The product retains the unshifted z
convention and has 116 operations and degree 1113.

## 2. Bounds available before recovering roots

The inherited weak transport bootstrap is applicable once Nk and Nt
are common units, before the norm has been decoded. It yields

    q>=16, X>=16, Y>=4096,
    0<R<q^4-2, E>=q^4>R+2, Cw>=0.

Since Nk=epsilon in {+1,-1}, k=R+epsilon+hE and h>=1. Thus

    k>=E, k>2R, c>kY>=EY>a=E+Y>=5, R<c.

Here EY>E+Y follows from E,Y>2. These are the only compiler-specific
inequalities used in the new separation proof. They do not depend on
an eliminated root or the desired sign epsilon=+1. Positivity gives
I>=c^2, c>=2, Delta>=2, Q>1 and d>0.

## 3. Exact separation estimate

At a vanishing norm, choose one coherent triple u,tau,f from a vanishing
factor and put y=(S-Lu-HLtau)/H. Then

    u^2=G, tau^2=A, f^2=D,
    d*y^2=Q*(v*f-b)^2-1,
    S=L*u+H*L*tau+H*y.

Every conjugate y' in a finite normal closure has f'=+-sqrt(D), hence

    |y'| < sqrt(Q/d)*(v*sqrt(D)+b).                 (1)

For full detail, let M=v*sqrt(D)+b>1. Then (v*f'-b)^2 lies in [0,M^2].
The absolute value of Q(v*f'-b)^2-1 is at most
max(1,Q*M^2-1), which is strictly less than Q*M^2 because Q*M^2>1.
Thus (1) covers imaginary as well as real conjugates; no total reality
is assumed.

The following two inequalities are the improved argument:

    sqrt(Q/d)*c*sqrt(D) < I*sqrt(G),              (2)
    sqrt(Q/d)*b < k*I^2*sqrt(G).                  (3)

For (2), the difference of the squared right and left sides after
multiplication by d is

    d*I^2*G-Q*c^2*D
      = I^2*[Delta^2*(I^2-c^2)-G] > 0.

Indeed I^2>=c^4, so I^2-c^2>=c^2; the bracket is at least
Delta*(Delta-1)*c^2-1>0.

For (3), a>=5 implies Delta=a^2+4a+3<2a^2. Since c>a and k>2R,

    R*Delta<2*R*a*c<k*a*c.

All quantities are integers, so k*a*c-R*Delta>=1. Moreover
c+R<2c<=c^4<=I^2. Consequently

    b=c+R+R*Delta*I^2 < k*a*c*I^2.

Finally

    d*G-Q*a^2*c^2
      = Q*(1+H*c^2)-G
      = (Q-1)+(Q*H-Delta)*c^2 > 0,

because Q=Delta^2 I^2, Delta>=2 and H>=1. Thus
sqrt(Q/d)*a*c<sqrt(G), proving (3).

Combining (1), (2) and (3), with T>0, gives

    |y'| < (T*I+k*I^2)*sqrt(G) = W*sqrt(G).      (4)

The coefficients 2 and 4 used in the earlier coarse root estimates
are unnecessary. This is why W uses just three arithmetic gates.

## 4. Recovery of the roots

By L=1+HW and (4),

    H*|y'| < L*sqrt(G).                          (5)

Also sqrt(A)>ell=kEY and sqrt(G)<(a+2)c<2(a+2)kY. As E>=2,
HE>=2H=8a+6>4(a+2), so

    H*sqrt(A)>2*sqrt(G).                         (6)

Suppose tau is irrational. In a finite normal splitting field some
automorphism sends tau to -tau. Subtract its image of
S=Lu+HLtau+Hy from that equation. The tau contribution has magnitude
2HL sqrt(A), whereas the other contributions have total magnitude
strictly below 2L sqrt(G)+2H W sqrt(G)<4L sqrt(G), by (4)-(5).
This contradicts (6). Hence tau is rational and, since tau^2=A is an
integer, tau is an integer.

If u were irrational, an automorphism sends it to -u while fixing
the now rational tau. Subtraction would give
2L sqrt(G)<=H(|y|+|y'|)<2L sqrt(G), a contradiction. Thus u is an integer.
Then y is rational by the displayed linear equation, and
f=(e-d*y^2)/Baux is rational because Baux>0. Therefore f is an integer
since f^2=D. Finally Q=(Delta I)^2 is an integer square, so the inherited
rational auxiliary-Pell saturation lemma applied to

    (Delta*I)^2*(v*f-b)^2-[(Delta*I)^2-1]*y^2=1

shows that y is an integer. That lemma is proved in package21,
NORM12_PROOF.md, Section3, using elementary integral Pell classification.

Since L=1 mod H, the linear equation gives

    u = S = X+ac mod H,

so gamma=(u-X-ac)/H is an integer. The complete signed normalized
interface is restored exactly as in package21. The inherited signed
rank argument resolves epsilon=+1 and recovers a blank halting tableau.
No new sign assumption is made here.

Conversely, for any canonical positive compiler witness, let its main
root be u=X+ac+H gamma and its first root be tau. The positive integer

    r=gamma+W*u+L*tau+y

satisfies S=Lu+HLtau+Hy and hence makes the norm zero. Thus the new
weight preserves existential equivalence in both directions.

## 5. Product and shifted system

The unchanged pair-ring norm evaluator writes N=N0^2-G*N1^2 with N1
divisible by 8 as an integer polynomial. Thus N is a square modulo64,
and cannot equal -2. If P=0, each of Nk,Nt,1+N is an integer unit;
therefore 1+N=1, N=0 and Nk=Nt are common units. Sections2-4 apply.
The polynomial parity argument is independent of the chosen weight.

The transport shift is the exact identity

    (K0+w)Cw+q-F-(z+1)(q-1)-1
      = (K0+w)Cw-F-z(q-1).

Every positive shifted solution is therefore a positive unshifted one.
Conversely the inherited compiler's true positive solutions have Cw>0,
X=wq=2^R and R>3q, whence w>q>F. Thus (K0+w)Cw-F>0, and the old
equation makes (z_old-1)(q-1)>0. Hence z_old>=2 and z=z_old-1>0.
This is the same justified shift as package22 RETAINED59_PROOF.md.
It applies after soundness, and is not used in the weak bootstrap.

## 6. Exact degree and counts

Each supplied variable has degree1; fixed coefficients have degree0.
The old base degrees remain

    c:5, E,a,H:6, Delta:12, A,G:22, I:11,
    D:34, Q,d:46, v:6, b:38, e:122.

The new weight has degree23, L degree29, and S degree11. In the pair
evaluator of package21,

    a0=H^2 L^2 A has degree92,
    V0=S^2+L^2G has degree80,
    C0=d(V0+a0)-H^2 e has unique leading term d*a0, degree138,
    C1=d*(2SL) has degree86.

Its next scalar square has degree276 and odd coefficient degree224.
The subtracted K term has degree264, and the scalar Z has degree238.
Hence N0 has degree552 and N1 at most500; therefore N0^2 has degree1104,
while G*N1^2 has degree at most1022. In particular there is no top-degree
cancellation. Writing q0=beta J and k0=eta+zeta, the leading form is

    N_top = 2^64 * i^48 * k0^128 * w^80 * s^192 * q0^656.

It is nonzero for every beta>0. The product has degree1104+7+2=1113.
For example, its coefficient of

    J^661 h z i^48 eta^128 w^81 s^193

is +2^64 beta^661. The sum of squares has degree2208, because the
norm squared is its unique highest-degree summand.

The original3 weight gates (two additions and a multiplication) are
replaced by3 gates (two multiplications and an addition); total count
is unchanged. Package21's final norm subtraction can be omitted in a
system that compares N0^2 with G*N1^2. The justified transport shift
saves one further gate. All other gates and all ports remain live.

| Presentation | Variables | Equations | Degree | Operations |
|---|---:|---:|---:|---:|
| Shifted system | 12 positive | 3 | max1104 | 110 |
| Unshifted system | 12 positive | 3 | max1104 | 111 |
| Product | 12 positive | 1 | 1113 | 116 |
| Shifted sum of squares | 12 positive | 1 | 2208 | 118 |

This gives a strict degree improvement over package20 (degree1145,
123 operations) and package21 (degree1353,116 operations) at twelve
positive coordinates. It is not an assertion of absolute minimality.
No unrestricted-integer extension of the new weight is asserted.

## 7. Executable evidence

`build_compact_norm12.py` emits all circuits and performs48 exact
signed norm checks using package21's independent eight-component
conjugate-product evaluator,48 exact transport-shift/SOS checks,
modulo64 parity checks, complete liveness/count audits, and three
modular leading-form checks. The uniform mathematical leading-form
proof above supplies exact degree, rather than relying on generic
numerical testing. The script rejects Python -O. No K215 halting
computation or inconsistency witness is constructed.

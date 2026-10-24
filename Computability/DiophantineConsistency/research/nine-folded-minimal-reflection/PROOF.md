# A shared minimal reflected parameter for the folded nine-variable equation

This new ordinary reduction keeps the entire source, the four native ports,
all fixed leaves, and the nine strictly positive inputs of the accepted
`research/nine-folded-reflected-parameter/` packet and its tight-folded parent. Its auxiliary parameter is
changed; it is not a pointwise identity between the two parent polynomials.
No Lean, internal-ZFC, new native calibration, or optimum claim is supplied.

| Complete tuple | Live operations | Exact degree |
|---|---:|---:|
| original31 | 406 = 238 mul + 150 add + 18 sub | 1,191,570 |
| compact54-sharp | 414 = 242 mul + 154 add + 18 sub | 1,316,546 |

The original and compact tuples are distinct coherent bindings. No port is
substituted individually. Both new circuits are supplied in full, with all
source nodes retained and all literal fixed values checked.

## 1. Exact parameter change

Use all definitions of the pinned parent proof. In particular,

```
U=N²w, Y=N²s, M=RY, P=2M²U, K=R+1+h(P-1),
A=M(U+1), B1=2R+1, W=bw, J=4A-5,
Q=3WC-2(W²-1), a0=1+(P²-1)K²,
m=K²(4cap-g)-16cap(C-KY)², Omega=Jm,
e=iC², F=1+(A²-1)*a0*e², V=A*a0*e,
Z=B1+jC, H=C+FZ, I=1+(G²-1)H²,
a=a0F, Vhat=GH, E0=Jn+Q,
Theta=E0-Omega*(V+Vhat).
```

The ambient contract is the same one as the parent: R,N>=8, b<=R,N,
and every b,g,h,s,w,C,i,j,n is positive. This is the already calibrated
source contract; it is not asserted for arbitrary fixed port assignments.
The sole mathematical change is

```
G_parent=F*(A+C+1)-A,
G_new=A*(F-1)+F=F*(A+1)-A.                                    (1)
```

The complete equation remains

```
(Theta²+Omega²(a-I))²-4Omega²*a*Theta²=0.               (2)
```

At the circuit level, the previous reflected parameter takes four operations.
The complete product Fminus1 already exists in the stored construction
F=1+e*(A*V-a0*e). The new parameter uses that exact existing product,
with one multiplication by A and one addition of F. It is universally
identical to the unshared three-operation expression F*(A+1)-A. The three
private old parameter intermediates are deleted and its G subtraction
is replaced by an addition, with one new product inserted. All other
operators and mapped operands are retained. The fixed source prefix does
not change. No literal Lambda remains in the new graph.

## 2. Bounds and positivity-first root extraction are retained

The parent's unconditional bounds use only the source and first-root core:
A>=33280, A>W, 1<B1<A, P>A, K>P>A, and a0>1. Thus F>a0>1.
For the new parameter,

```
G_new-F=A*(F-1)>0.                       (3)
```

Consequently G_new>F, G_new>=3 and H>2F, exactly as needed in the
parent's unshifted-carrier proof. In particular
I>=G_new²>F²>a0F=a, so the radicands are unequal unconditionally.
The majorants have the same exact defects

```
V²-a=a0*(a0e²-1)>0,  Vhat²-I=H²-1>0.                (4)
```

For completeness, the margin argument precedes all integrality and Pell
classification. If m=0, its exact defining equality and g>0 imply
|C-KY|<K/2, whence C>K>A>W, Q>0 and E0=Jn+Q>0; (2) is E0^4,
not zero. If m<0, factor (2) over the reals. Some signs satisfy

```
E0=Jm*L,  L=V+Vhat +/-sqrt(a) +/-sqrt(I)>V-sqrt(a)
          >(a0-1)/(2A)>0.
```

The parent lower bound gives J*(a0-1)/(2A)>2W². Hence E0<-2W²,
contrary to E0=Jn+3WC-2W²+2>-2W². Thus m>0 on every zero.
It follows that C>K>B1>1. This argument only needs (3)-(4); it never
uses the sign of G modulo F, a rational root, or a projection conclusion.

As in the parent, the unequal positive radicands have a nonzero rational
signed root sum, so both roots are rational and hence integral. Since
F=1 modulo a0, gcd(a0,F)=1. Therefore a0 and F separately are squares.
Write tau²=a0 and f²=F, with tau,f>0. The ordinary Pell equations give

```
f=chi_A(q), e*tau=psi_A(q), q>=1,
H=psi_G(t), t>=1.                                    (5)
```

No signed-G branch is present: the actual new G is positive by (3).

## 3. Reflection modulo F and the unchanged main index

The new parameter has the two exact congruences

```
G_new=-A modulo F,   G_new=1 modulo C.                (6)
```

The second follows from F=1 modulo C. The integer Pell recurrence gives,
for every integer A and every natural index t,

```
psi_(-A)(t)=(-1)^(t-1)*psi_A(t)  for t>=1.            (7)
```

At index zero both sides are zero if stated using the usual parity version.
Identity (7) follows directly from psi(0)=0, psi(1)=1 and
psi(t+2)=2A*psi(t+1)-psi(t). No modular division is involved.
Since H=C modulo F, (5)-(7) imply

```
psi_A(t)=+C or -C modulo f.                          (8)
```

The parent's folding proof already works with signed residues. Modulo
f=chi_A(q), the addition identities give
psi_A(t+2q)=-psi_A(t) and psi_A(2q-t)=psi_A(t).
Every index has a representative r in [0,q] up to sign, and the signed
values lie in (-f/2,f/2), since f>2psi_A(q). Moreover
0<C<=e*tau=psi_A(q)<f/2. Thus (8) recovers

```
C=psi_A(p),  1<=p<=q,  t=+p or -p modulo 2q.          (9)
```

C>B1>1 makes p>=2. Strong divisibility gives p|q. Writing q=pu,
the binomial expansion of the Pell unit modulo C³ yields
psi_A(q)=u*chi_A(p)^(u-1)*C modulo C³.
Because C²|e*tau and gcd(chi_A(p),C)=1, C|u, hence C|q.
The second congruence in (6) now gives H=t modulo C, and H=B1 modulo C.
Together with (9), this gives p=+B1 or -B1 modulo C.
But C=psi_A(p)>=A*p and B1<A imply
0<p+B1<C and |p-B1|<C. Therefore p=B1, exactly as in the parent.

Finally (2) has integral roots, so E0 is divisible by J and J|Q.
The recovered a0 square, C=psi_A(B1), positive margin and J|Q are
precisely the retained numerical ratio/source boundary. The existing
whole-source decoder therefore gives the same source zero and ordinary
refutation. This proof does not assume auxiliary-index parity in soundness.

## 4. Actual positive auxiliary witnesses in completeness

Start from any source/ratio witnesses of the retained boundary. Thus
C=psi_A(B1), a0=tau², m>0 and J|Q. The same finite determinant-one
matrix period modulo C²*tau supplies a positive q with C²*tau|psi_A(q).
Set i=psi_A(q)/(C²*tau)>0. Then F=chi_A(q)², unchanged from the parent.
Define the new positive G by (1).

Let T>0 be a period of its determinant-one recurrence matrix modulo F.
Choose arbitrarily large t=B1+k*T*C. By the first congruence in (6),
recurrence reduction and B1=2R+1 odd give

```
psi_G(t)=psi_G(B1)=psi_(-A)(B1)=psi_A(B1)=C modulo F.  (10)
```

The oddness of this actual index is essential here; no parity assumption
on an arbitrary soundness index t was used. Also G=1 modulo C gives
psi_G(t)=t=B1 modulo C. For large t, let H0=psi_G(t) and
z=(H0-C)/F. This is an integer, z=B1 modulo C since F=1 modulo C,
and z>B1. Thus j=(z-B1)/C is a strictly positive integer and H=H0.
The new I is a square. This constructs actual witnesses rather than
subtracting an old j coordinate without a positivity proof.

Let Dproof=1+(A²-1)C². As in the parent, F>Dproof and
Vhat=G*H>2F>2Dproof. The unchanged polynomial inequality gives
W²+Q/J<2Dproof, so the positive integer

```
n=m*(V+Vhat+sqrt(a)+sqrt(I))-Q/J
```

makes (2) vanish. All source variables b,g,h,s,w,C are retained, while
i,j,n are freshly chosen. The whole original31 and whole compact54-sharp
calibrations remain separately applicable. No pointwise equality between
old/new G values, j values, or final polynomial evaluations is asserted.

## 5. Exact degree and finite audit scope

Put d=deg A, r=deg R and Wmax=max source weight. The degree of the
new G equals that of the preceding reflected parameter: 9d+2r+8.
The stored Fminus1 has the same highest degree as F, 8d+2r+8.
Compared with the original tight-folded parameter, the reflected G,
Vhat and Theta bounds are one smaller and the I bound two smaller.
The present step changes no one of those reflected degree bounds.
All other bounds remain F=8d+2r+8, H=8d+3r+8 and Omega=5d+2Wmax+3.
The exact centered identity of the parent is unchanged. Its four summand
bounds become

```
52d+12r+8Wmax+44,
60d+13r+8Wmax+49,
66d+14r+8Wmax+54,
50d+10r+8Wmax+38.
```

The third is uniquely largest, with nonzero leading form
4*LH(Omega)^4*LH(a0)^2*LH(e)^2*LH(Vhat)^2.
The checker verifies all literal degree bounds and nonzero leading
homogeneous values with every actual fixed integer. A nonzero value
modulo a prime certifies that homogeneous component over Z; this is not
an empirical estimate of degree. It gives the exact degree
1,191,570 for (d,r,Wmax)=(16357,7931,115), and1,316,546 for
(18069,8787,115). The larger raw syntactic bounds are kept separately.

The finite parity, folding, positivity, modular and matrix-period controls
supplement this unbounded proof. They are not its justification. The
producer executes no parent emitter. The independent checker checks every
retained node, all three deleted private nodes, the single inserted node and shared Fminus1,
the actual G formula, the complete norm, fixed payload values, degree
certificates and targeted mutations. The pinned accepted parent supplies
all unchanged ordinary source, cofinality and numerical ratio results.

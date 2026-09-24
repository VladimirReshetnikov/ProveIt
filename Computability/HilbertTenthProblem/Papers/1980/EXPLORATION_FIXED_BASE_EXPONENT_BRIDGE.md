# A fifteen-operation positive fixed-base exponent bridge

The retained43-operation kernel already computes the numeral-expression
`4a+3`. Reusing that register adds the exact endpoint relation

    W=B^(x+2), B=2^d,

in **15 additional operations:7M+8A**, including the construction of
`t=x+2`, its conversion to the binary exponent `u=d*t`, and the
strengthened raw-input bound. Both B and d are fixed positive numerals.
The raw input x remains a positive variable. This saves two operations
relative to the variable-base17 bridge.

The [checker](../verification/explore_fixed_base_exponent_bridge.py)
and [receipt](../verification/explore_fixed_base_exponent_bridge.json)
also supply an exact **82=44M+38A** conditional source, with33 positive
existential coordinates and21 equations. Its cyclic neighborhood has
offsets `0,-1,-h`; its End marker is at distance `x+2` from Start.
The fixed helical-tableau reduction connecting that neighborhood and
marker arrangement to machine halting is external to this note.
Consequently this component alone does not establish a complete
universal82 theorem.

## 1. Retained facts and the new four equations

Use the positive kernel, compiler, two-marker decomposition, and
inverse packing of the [complete84 source](FIXED_RAW_UNIVERSAL_84_PROOF.md).
Write

    A0=a+2, Delta=A0^2-1=a^2+4a+3, H=4a+3,
    J0=2r+1, X=2^J0, c=psi_A0(J0),
    q=B^N, P=B^h, 1<=h<=N,
    q^2<=r<q^4, a>J0, a>X>q, B=2^d, d>=4.          (1)

Here `psi` and `chi` are the second and first Pell coordinates, with
`(chi(0),psi(0))=(1,0)` and `(chi(1),psi(1))=(A0,1)`.
The registers `A` and `a4m5` in the executable source are Delta and H.
They are already paid inside the unchanged43-operation kernel.

Construct `t=x+2` and `u=d*t`, and strengthen the old word bound to

    C+alpha+u=q.                                     (2)

Keep the marker decomposition

    C=CS+Z+W,

where all coordinates are positive. Before interpreting any state or
power, these equations give `0<Z<C<q`, `0<W<C<q`, and `0<u<q`.
They preserve every preliminary kernel bound in the complete84 proof.
In particular the kernel and geometry recover (1) before applying
the new exponent argument or typing the full C word.

Supply the five positive coordinates `kappa,mu,delta,phi,rho` and impose

    kappa=u+delta*(a+1),
    c=kappa+phi,
    mu^2=1+Delta*kappa^2,
    mu=W+a*kappa+rho*(4a+3).                         (3)

The strengthened bound replaces the old bound; (3) adds only four
equations. The positive endpoint W is a separate supplied coordinate.

## 2. Exact recovery of the exponent

The positive norm solution has

    kappa=psi_A0(v), mu=chi_A0(v), v>0.

The gap `c=kappa+phi` and strict increase of psi give `v<J0`.
Reducing the recurrence modulo `A0-1=a+1` gives
`psi_A0(v)=v mod(a+1)`, so the first equation of (3) gives
`v=u mod(a+1)`. But

    0<v<J0<a+1, 0<u<q<J0.

Hence v=u. Neither this step nor the preliminary bound assumes that
the input has already been identified with a tableau length.

The elementary Pell identity for base2 is

    chi_A0(u)-a*psi_A0(u)=2^u mod(4a+3).             (4)

Indeed `Delta-a^2=4a+3`, so substitution of a for the formal square
root of Delta sends `A0-sqrt(Delta)` to2 modulo that modulus.
This uses polynomial substitution and requires no modular division.
Equation (3) and (4) therefore give `W=2^u mod H`.

The bounds needed to turn the congruence into an equality are strict:

    2^u<2^q<2^r<X<a<H, 0<W<q<H.                     (5)

The first two inequalities follow from `u<q<r`, and `X=2^(2r+1)`.
Thus

    W=2^u=2^(d*(x+2))=B^(x+2).                      (6)

In particular `t=x+2<N`. The proof only needs the supplied bound
W<q; it does not assume a prior interpretation of W as a power.

## 3. Positive completeness and the raw-input slack

Suppose a genuine typed cyclic word has Start at0 and End at t,
where `t=x+2`, `N>t`, and W=B^t. Choose dummy bits arbitrarily within
the compiler's permitted positions. Every cell is at most B-2, so

    C<=(B-2)J, J=(q-1)/(B-1), q-C>=J+1.

Since `N-1>=t` and `u=d*t`,

    J>=B^(N-1)>=B^t=2^u>u.

Consequently `alpha=q-C-u` is strictly positive. This slack proof
does not require every genuine cell to be even.

At the actual fresh kernel parameter A0 choose

    kappa=psi_A0(u), mu=chi_A0(u),
    delta=(kappa-u)/(a+1), phi=c-kappa,
    rho=(mu-a*kappa-W)/(4a+3).                        (7)

The index and power congruences prove integrality. Here u>=12, so
`psi_A0(u)>u` gives delta>0; `u<q<J0` gives phi>0. Finally

    mu-a*kappa=2*kappa-psi_A0(u-1)>kappa>=2A0>W.

The positive modulus makes rho>0. Thus every newly supplied Pell
coordinate is positive, including the case x=1. The same fresh
actual packed-index kernel construction used by84 supplies its
seventeen positive coordinates. No earlier numerical packed witness
is identified with this one.

The raw-input bound cannot simply be discarded. In a genuine bridge
with delta>d, replacing

    x by x+(a+1), delta by delta-d

preserves every equation of (3), every other coordinate, and the
positive domains. It preserves the encoded word and endpoint while
changing the raw input. Equation (2) excludes this ambiguity. The
checker records positive instances of this alias mechanism.

## 4. Helical local transport and its positive quotient

The conditional82 source uses the same fixed homogeneous three-site
compiler as84, with genuine End code1 and Start code CS=R. It changes
only the geometry of the neighborhood: spatial right is a shift by1,
and next time is a shift by h. Put D=q-1. For a typed word, let

    Rword=B*C-kR*D,
    Yword=P*C-kY*D,
    Factual=DC*C+DR*Rword+DY*Yword.

The unchanged coefficient bounds give `0<Factual<q-1`. Its congruence
is represented by

    (DC+B*DR+DY*P)*C=F+z*D.                          (8)

The numeral `DC+B*DR` is fixed. Computing `DY*P`, adding that numeral,
multiplying by C, computing zD, and adding F costs exactly5 operations,
the same as the older consecutive-shift transport.

For a genuine nonempty state at every cell, C>=J. Since B and P are
multiples of B and at least B,

    kR>=1,
    kY>=floor(P/(B-1))=(P-1)/(B-1)=align>=1.

Thus the exact quotient in (8) is positive:

    z=DR*kR+DY*kY>=DR+DY*align>0.                    (9)

For soundness, bounded F and bounded actual F make their congruence
exact, after the kernel has typed Z and (6) has inserted the two
markers. The homogeneous occupancy clauses now propagate occupancy
under the spatial shift1 directly. Start provides occupancy1, so
every cell is a genuine state. The local relation holds at offsets
`0,-1,-h`, Start is unique at0, and End is unique at t.

This proves the arithmetic encoding of that finite cyclic marked
relation. It does not by itself establish a fixed-machine tableau
interpretation of the relation. In particular the old consecutive
shift completeness theorem is not silently substituted here.

## 5. Exact operation ledger

The retained source already supplies `bounded=C+alpha`,
`A=Delta`, and `a4m5=4a+3`. Append:

| Register | Primitive operation |
|---|---|
| t | x+2 |
| u | d*t |
| raw_bound | bounded+u |
| ap1 | a+1 |
| index_product | delta*ap1 |
| index_rhs | u+index_product |
| pell_gap | kappa+phi |
| kappa2 | kappa*kappa |
| scaled_kappa2 | Delta*kappa2 |
| norm_rhs | scaled_kappa2+1 |
| mu2 | mu*mu |
| modulus_multiple | rho*a4m5 |
| difference_multiple | kappa*a |
| exponent_partial | W+difference_multiple |
| exponent_rhs | exponent_partial+modulus_multiple |

The five equality comparisons are `raw_bound=q` (replacing the old
bound), `kappa=index_rhs`, `c=pell_gap`, `mu2=norm_rhs`, and
`mu=exponent_rhs`. The adapter is7M+8A=15. Multiplication by d is
explicitly charged even though d is a fixed numeral.

The complete conditional schedule is

| Part | M | A | Total |
|---|---:|---:|---:|
| Geometry |3|2|5|
| Existing bound register |0|1|1|
| Helical transport |3|2|5|
| Powers and inverse packing |6|5|11|
| Two direct marker additions |0|2|2|
| Retained kernel |25|18|43|
| Fixed-base exponent adapter |7|8|15|
| **Conditional source** |**44**|**38**|**82**|

All33 positive coordinates and21 source equations are listed in the
checker and saved receipt, including the unchanged acyclic correction
for the auxiliary Pell equation. Fixed aliases depend only on compiler
numerals, never on x.

## 6. Verification scope

The checker independently expands all21 residuals and verifies all82
primitive instructions. It checks the base-two Pell congruence over
a finite grid and composes the outer helical transport, two-marker
encoding, positive slacks, actual packed population, and positive
adapter witnesses on common q,P,C,Z,W values. Mixed dummy bits at
both markers include examples with Z not divisible by B.

Those numerical examples use moderate Pell parameters to check the
adapter; they do not materialize the immense full kernel witnesses at
the actual packed index. The retained mathematical converse covers
those witnesses. The fixed helical-tableau semantic interface remains
a separate proof obligation, and no universal82 claim is made by this
component receipt.

# Bound sharing and direct lanes give a filtered paired queue in64/69/72

The [polynomial-input extension](input_bridge_filtered_polynomial_obstruction.md)
also excludes repair by any fixed positive even integer-polynomial
initial-value substitution alone. Additional filters remain outside that theorem.

A subsequent [raw-input obstruction](native_controller_paired_raw_obstruction.md)
proves that this one-carry family has no universal representation compiler,
including with its paid fixed block alignment. The exact component theorem
and counts below remain valid.

Two literal savings preserve the exact projection of the reviewed
[filtered paired66/71/74 source](native_controller_paired_filter71.md).
The paid filter bounds its first three fields before power recovery, so
only the fourth field needs a separate bound. Directly computing both
lane transports then removes the unused scalar read/transport registers.

The resulting components cost **64=32M+32A** for the filtered queue,
**69=35M+34A** with the fixed affine carry controller, and
**72=37M+35A** with fixed block alignment. They retain ordinary positive
input x and the same positive finite-run semantics. No universal compiler
or acceptance theorem has been supplied; the complete universal bound
remains76. The frozen66/71/74 packet is unchanged.

## 1. The first saving is a paid fourth-field bound

Write F0,F1 for the append rails and F2,F3 for the read rails. Keep the
four-field Horner packing and the raw44-operation Boolean ternary kernel
from [Boolean55](input_bridge_boolean_ternary60.md), including

    r=F0+qF1+q^2F2+q^3F3,
    X=wq, Y=3s+1, r+bound_beta=X.                       (1)

The filtered source already computes A=F0+F1 and H=A+F2, then imposes

    H+H+1=q.                                          (2)

Replace its old two-operation joint bound

    joint=A+(F2+F3); joint+alpha=q

by the one-operation bound

    F3+alpha=q.                                       (3)

Every supplied Fi and alpha is strictly positive. This is not deletion
of the last bound on an otherwise untyped field: equation(2) bounds the
first three fields, and(3) bounds the fourth. The proof below establishes
these facts before applying any power or digit interpretation.

Using only this saving gives the reference sources65/70/73. Their
instructions and residuals are preserved alongside the further optimized
sources, so the two changes can be audited separately.

## 2. Raw-kernel bootstrap under the changed bound

Before assuming that q is a power or any Fi has Boolean digits, the
positive sum H=F0+F1+F2 is at least3. Equation(2) therefore gives

    q=2H+1>=7, F0,F1,F2<q.

Equation(3) gives0<F3<q. Thus the same actual Horner packing satisfies

    q^3+q^2+q+1 <= r < q^4, r>=400.                    (4)

The paid bound and Y=3s+1 give X>r, Y>=4. Put

    E=XY, a=Y(X+1), A0=a+3, Delta=A0^2-1,
    P=2XY^2+1, J=2r+1.

Then E>r+1, a>J, P>A0 and6XY^2>a. These are the preliminary facts used
in Section2 of the raw Boolean55 proof; all its lower thresholds have
strengthened. For clarity, the recovery steps are as follows.

The first Pell norm has k=psi_P(n) with n=r+1 modulo E. Since E>r+1,
n>=r+1. The positive ratio interval Yk<c<(Y+1)k and P>A0 give main
index p>=n+1>=r+2>=402. In particular the same relaxed-rank and
half-parameter bounds hold:

    c>A0*(A0^2-1)^2, c>J, c>2p.

The unchanged auxiliary norms recover p=J and their main-base index
divisible by c, with auxiliary parameter greater than1 and f>2c. The
generic signed positive-branch theorem applies exactly as in Boolean55,
forcing r even. The first index is n=r+1: its next congruence
representative exceeds J, whereas P>A0 and c>k preclude n>p.

The lower ratio estimate is used first. It gives Y>=X^r and
a>X^(r+1). The upper estimate is then justified and has error at most
24r/(X+1). The retained exponent recurrence gives X=3^J modulo6a+8.
Both positive representatives are below that modulus: X<a and

    3^J=3*9^r < X^(r+1) < a,

using X>r>=400. Hence X=3^(2r+1). Since q divides X and q>=7,
q=3^t for t>=2. The now-small ratio error and binomial tail recover

    Y=floor((X+1)^(2r)/X^r).

As Y=3s+1 and3 divides X, the central binomial coefficient is1 modulo3.
Its3-adic valuation is zero, so every ternary digit of r is0 or1.
The bounds Fi<q were already proved, so there is no carry between the
four q-sized fields: each Fi is a positive native Boolean ternary word.
These are applications of the explicit raw-kernel arguments, not an
assumption that the old joint-bound typing theorem remains true after
an equation is changed. No divisibility of Y by q is used.

Now H=(q-1)/2 is the ternary repunit. In(2), the positionwise residual
`a0+a1+d0-1` lies in[-1,2]. Successive reductions modulo3 force every
residual to vanish, giving exactly

    a0+a1+d0=1.                                       (5)

Also F3<q is Boolean, so F3<=H. Consequently the old joint bound is
recovered as a theorem:

    sum Fi=H+F3<=2H=q-1.                              (6)

The signed kernel theorem gives r even; since q is odd, this is the same
as even sum Fi. Thus the changed bounds yield exactly the field typing
and filter of the frozen source.

## 3. Direct lane transports save one more addition

Keep the positive initial witnesses I0,I1 and their paid equation

    I0+I1=2x,

as well as2x+width_beta=W and q=W*L. The previous source computed
D=F2+F3 and imposed its scalar transport, while separately certifying
the first lane. Once both lanes are explicit, those scalar registers
are unnecessary. Compute

    lane0_tail=W*F0; lane0_transport=I0+lane0_tail,
    lane1_tail=W*F1; lane1_transport=I1+lane1_tail,

and compare F2=lane0_transport, F3=lane1_transport. Retain the already
computed append sum A=F0+F1 for the filter.

In the reference source, the first pair was already paid. Delete

    D=F2+F3; scalar_tail=W*A; scalar_transport=2x+scalar_tail

and replace its scalar comparison by the second-lane comparison. The
three removed instructions are1M+2A; the two added instructions are1M+1A.
This saves one further addition. Adding the two lane equations and the
initial-sum equation recovers the old scalar transport exactly. Conversely
the old scalar equation and first lane recover the second lane. No
supplied coordinate changes and no hidden summation is needed in the DAG.

## 4. Exact positive projection and unchanged controller

The optimized64 source projects exactly to the same filtered paired runs
as the frozen66 source:

- q=3^t, W=3^m, with m>=1 and t>=m+1;
- positive Boolean ternary initial words I0,I1, with I0+I1=2x<W;
- a synchronized t-step pair of width-m Boolean queues from(I0,I1) to(0,0);
- all four read/append streams positive, with the local rule(5).

The field typing and joint bound have just been proved. The direct lane
identities imply the initial Boolean words, the FIFO recurrence and zero
endpoints as in the reviewed paired63 proof. Conversely, any path in this
predicate gives all equations, and its parity is automatic:

    sum Fi=2x+(W+1)(F0+F1) is even.

The joint bound follows from(5), independently of the kernel. Thus the
raw Boolean55 positive converse applies at these exact fields. Replace
only its old joint slack by

    alpha=q-F3>0.                                     (7)

More explicitly, alpha_new=alpha_old+H. In the reverse direction,
alpha_old=alpha_new-H=q-H-F3>=1 by(6). Every other kernel and outer
coordinate stays unchanged. This proves both directions of the exact
projection without padding the path or silently changing its fields.

For fixed integers u0,u1,v0,v1,h,cs,cf satisfying2cf=h+u0, keep the
five-operation controller from the frozen71 source:

    (v0-u0)F0+(v1-u0)F1+u1F3=cf-cs.                  (8)

Its full graph is

    3c_next=c+h+u0*d0+u1*d1+v0*a0+v1*a1,
    c_initial=cs, c_terminal=cf.

Equation(5) and q=2H+1 make(8) exactly its global carry equality; successive
division modulo3 recovers every integral intermediate carry. This gives
the69 source with the same full labelled relation as71. No selected-state
restriction, code alphabet or ordinary-input normalization is inferred.
The previously proved terminal-tail and wrong-endpoint finite-input
theorems apply unchanged because the projected runs are identical.

For fixed ell>=2, retain the three paid block-alignment instructions for
`(3^ell-1)Jblock=q-1` and `(3^ell-1)Kblock+1=W`, using the computed q-1 register.
They give exactly ell|t and ell|m with positive Jblock,Kblock. This yields72 and
does not supply a block code or a compiler.

## 5. Complete literal ledgers and positive examples

All field, kernel, initial-split and width coordinates remain strictly
positive. H is a computed register. Signed controller coefficients and
computed registers do not add supplied witnesses.

| Variant | M | A | Total | Equations | Positive witnesses besides x |
|---|---:|---:|---:|---:|---:|
| Changed bound, scalar transport retained | 32 | 33 | 65 | 19 | 29 |
| Same plus carry controller | 35 | 35 | 70 | 20 | 29 |
| Same plus block alignment | 37 | 36 | 73 | 22 | 31 |
| Changed bound, both lane transports explicit | 32 | 32 | 64 | 19 | 29 |
| Same plus carry controller | 35 | 34 | 69 | 20 | 29 |
| Same plus block alignment | 37 | 35 | 72 | 22 | 31 |

The [checker](native_controller_paired_filter70.py) independently expands
every source polynomial for all six complete schedules and verifies the
inherited auxiliary-norm correction. It checks the scalar/paired identity
and that the removed registers are absent from the optimized DAG.

The64 source admits every ordinary positive x. Choose a positive Boolean
split I0+I1=2x, a power W=3^m>6x, and Hm=(W-1)/2. The frozen filter's
three-sweep construction gives

    q=W^3, F0=W*Hm, F1=Hm-I0,
    F2=I0+W^2*Hm, F3=I1+W*(Hm-I0).

Every field is positive; all equations hold with(7), and the full positive
Pell extension follows as above. Choosing m a multiple of any fixed ell
also aligns t=3m. With identically zero carry data this gives positive72
examples for every x; it does not prove completeness for other controllers.

The nonzero controller from the frozen71 packet also persists exactly:
x=1, W=3, q=81, initials(1,1), fields(9,3,28,10), append weights(-2,4),
read weights(2,3), h=-2 and cs=cf=0. Its carry sequence is(0,1,1,0,0).
The changed slack is alpha=71, in place of the old joint slack31.
The remaining outer and kernel coordinates are unchanged.

## 6. Evidence boundary

The checker tests35910 arbitrary positive pre-power tuples with the new
bound, including nonpowers q, and61020 bounded field tuples through q=81
for the no-carry typing/parity projection. It constructs four positive
maps for each of200 ordinary inputs, including block lengths2,3,5, and
checks the nonzero controlled69 witness. These finite tests supplement
the raw-kernel and exact-projection proof. The huge Pell coordinates are
supplied parametrically by the reviewed positive converse, not numerically
materialized. The [saved receipt](native_controller_paired_filter70.json)
is replayed by default.

Independent full proof, source, and default-replay review passed. Universality,
ordinary-input simulation under a chosen nontrivial controller, and a
correct halting interface remain separate obligations.

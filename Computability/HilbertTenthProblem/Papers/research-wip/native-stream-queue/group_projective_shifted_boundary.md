# Reflect the fixed alphabet and share a shifted boundary

A fixed reflection of the macro alphabet, together with a different common
origin for the four histories, saves **one addition** in the complete
[projective compiler with computed kernel fields](group_projective_computed_kernel_fields.md).
It adds no witness or comparison and preserves that construction's exact
degree. The same ordinary universal input sets are represented after the
fixed alphabet is reflected once.

For m=2^h padded edges, paid physical-port cost p and sparse flow cost f,
the new comparison certificate costs

    C = 3m+3h+p+184+f−3min(h,3),
    M = m+2h+80+f_M−d_M,
    A = 2m+h+p+104+f_A−d_A.                       (1)

The unchanged common-register savings satisfy d_M+d_A=3min(h,3).
The four-field variant has22 comparisons,m+36 positive witnesses and
polynomial cost C+65, degree12m+232. The six-field variant has20
comparisons,m+34 witnesses and polynomial cost C+59, degree24m+444.
Thus the two polynomial base constants are249 and243 respectively.
The ten-letter example with m=16,h=4,p=4,f=19 now costs258 comparison
operations or317 polynomial operations in the six-field variant.
It remains an illustrative table, not a numerical universal alphabet.

## 1. A fixed reflection preserves the universal vector query

Let J0=diag(−1,1). Conjugating both fixed matrix blocks by J0 sends a
unit upper or lower shear of sign epsilon to the same shear of sign
−epsilon. Therefore each fixed physical code is transformed simply by
swapping labels1 with2,3 with4,5 with6 and7 with8. The order of letters
is preserved. In particular this is not word inversion, which would
also reverse their order. Hub idle label0 is unchanged.

For each original pair of macro products A,B, the reflected products are
J0*A*J0 and J0*B*J0. The established endpoint uses v=(−1,u), where
u=alpha*x+beta+1. Since J0*v=(1,u) and J0*e2=e2,

    A*v=B*v=e2
      iff (J0*A*J0)*(1,u)=(J0*B*J0)*(1,u)=e2.    (2)

Reflect the one fixed universal alphabet, including its inverse codes,
once. Equation (2) and the [projective theorem](group_projective_zero_mortality6.md)
then give exactly the same universal ordinary-input predicate. The program
numerals alpha,beta are unchanged. The macro lengths, underlying paths,
state-flow cost and multiplicities of physical ports are preserved: only
pairs of physical labels are permuted. The displayed m,h,p,f counts are
therefore unchanged by this compiler transformation.

For a general fixed table the new certificate represents paired action
on(1,u) ending at e2. It is not asserted to recognize the old action on
(−1,u) using the same unreflected table. In fact an old target code L_r
sends(−1,r+1) to e2 but fails this new endpoint; its reflected code passes.

## 2. Five boundary gates and a shared range coefficient

Supply the same positive height_slack and compute

    input_product=alpha*x,
    u=input_product+(beta+1),
    D=u+height_slack,
    C0=D−1,
    Iodd=C0+u.                                   (3)

This costs **5=1M+4A**. Continue to compute the radix B=8D in its
existing gate, but shift every signed state coordinate by C0, rather
than by D. The initial shifted state is

    (D,Iodd,D,Iodd),

and its required terminal state is

    (C0,D,C0,D).                                 (4)

Thus no separate computed terminal D+1 is needed. Crucially, the
already shared range coefficient still costs one addition:

    2D−1=D+C0.

The range mask and every joined AND region remain literally unchanged.
Deleting D−1 instead would lose this sharing, which is why merely changing
the sign of the initial vector without shifting the origin gives no net
saving in the full compiler.

As before u>=3, D>u and C0>=3. All initial and terminal entries in (4)
are strictly between zero and2D. The initial second entry satisfies
C0+u<=2D−2. No positivity assertion depends on a comparison being used
before it is proved.

## 3. The same typed history argument with origin C0

All typing, controller, output and scalar-bound comparisons are retained.
Their actual arithmetic registers are unchanged, including the scalar
pretyping bounds and the AND at scale16P^(m+18). Consequently the
[parent range proof](group_range_projective_compiler.md) first establishes
P=B^t for t>=1, the exact macro word, mutually exclusive physical selectors,
exact selected products, and canonical history digits

    0<=X_i(j)<2D.                                (5)

The four transport comparisons now are

    B*(H_i+delta_i)=H_i+E_i*P−I_i,
    delta_i=Z_(2i)−Z_(2i+1)−C0*(S_(2i)−S_(2i+1)), (6)

with I,E from (4). Only the existing offset multiplications change
operands; no arithmetic is added.

The constant residual coefficient I_i−X_i(0) has absolute value less
than2D<B, so reduction modulo B forces the correct initial state.
At an interior cell the coefficient is

    X_i(j−1)+epsilon*(X_(i xor1)(j−1)−C0)−X_i(j).

By (5), the signed source lies in[−D+1,D]. The displayed coefficient
lies strictly between−3D and3D, hence strictly between−B andB. Successive
reductions modulo B force all coefficients to vanish. The terminal
coefficient then gives exactly (4). Subtracting C0 recovers the signed
trajectory on(1,u) ending at e2. Canonical zero digits are permitted in
this soundness argument.

Conversely take a genuine macro word satisfying that paired action.
Choose a power of two D larger than u and larger than one plus the
absolute value of every signed trajectory coordinate, with8D>m. Then
height_slack=D−u is positive and every shifted digit C0+v lies strictly
between0 and2D. The unchanged bounds yield positive history and output
slacks, edge and output hats, and radix slack. The same exact AND
converse supplies the one complete positive native extension. All
transport comparisons (6) hold. This proves the complete generic
paired-action theorem, and (2) supplies its universal corollary.

This proof preserves accepted inputs after the fixed reflection. It
need not preserve a particular parent witness tuple: a tuple touching
a range boundary may require a larger D after the origin changes.
No unsupported positive-witness bijection is claimed.

## 4. Source, degree and validation

The [checker](group_projective_shifted_boundary.py) starts with each of
the frozen four- and six-field sources. It removes only the gate computing
history__V=D+1, and changes four boundary operations and four
offset multiplications as recorded in the literal source. In particular the first
endpoint is C0, the second is D, the first initial value is D, and the
second is C0+u. All sources remain topologically valid.

Only the first four residuals change. They have degree at most three.
Every other residual and every joined-region register is identical to
its parent on the same supplied assignment. Therefore the unique highest
native residual and its nonzero highest form are unchanged. The exact
polynomial degrees remain12m+232 and24m+444, as asserted in (1).

Across four tables and both variants the checker verifies2,048 complete
residual identities, including512 signed off-zero cases. It checks every
new transport against the direct formula (6), every retained residual
against the parent, and the full sum-of-squares difference against the
four changed squares. Eight weighted univariate slices verify degree
and leading-coefficient preservation.

Another512 arbitrary words verify the fixed conjugation identity without
reversing letter order. Six genuine reflected endpoint fixtures construct
all positive outer coordinates and check the full joined AND and retained
outer equations. The native Pell coordinates in these fixtures remain
explicit placeholders; their positive extension is proved parametrically,
not claimed to be numerically materialized. The unreflected code rejection
is also checked.

Run the checker normally to compare its deterministic
[receipt](group_projective_shifted_boundary.json); use `--write` only to
regenerate it. No numerical universal alphabet or improvement below the
separate75/88 global bounds is claimed.

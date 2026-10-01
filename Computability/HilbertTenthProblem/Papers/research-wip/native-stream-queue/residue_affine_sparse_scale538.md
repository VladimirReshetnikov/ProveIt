# A positive computed scale gives sparse universality in538 operations

The [literal source](residue_affine_sparse_scale538.py) improves the
[540-operation sparse compiler](residue_affine_sparse_bound540.md) to
**538=193M+345A**, with **67 positive witnesses**, **seven comparisons**
and degree **at most5091**. Its certificate has518 operations. The
[receipt](residue_affine_sparse_scale538.json) records the complete source
and deterministic exact checks.

The packing scale is now a positive computed bound. Its repunit equation
is enforced as an integer unit inside the existing product. A negative
repunit sign is ruled out by recovering native dyadic scale before applying
the complete AND theorem. This order matters because the added factor
initially allows the old native product to be negative.

The new and parent positive zeros are identical on the supplied coordinates.
Thus the same fixed literal U21, program parameter E=3^e and ordinary
positive input x retain their full universal representation. The paid
loader prefix, remainder comparison and complete chronology remain.
This is an independent substrate result above the established75/87 bounds.

## 1. Literal scale rewrite and factorization

Use the parent notation: nonnegative selector words E_e with sum J,
nonnegative quotient and remainder words W,R,S, positive quotient word
U=W+J, prime-selected words Z_p, and

    V=U+sum_(p>2)(p−2)Z_p.

The increment and decrement selections have positive supplied hats
YI_hat,YD_hat, and the positive global slack is beta. Keep

    h=E+x+F+eta>=4, B=C_B*h,
    C_B dyadic, C_B>=max(4,edge_count+1,state_count+2,3*pmax+1).

The old source defines P=(B−1)J+1 and compares

    G=V+YI_hat+YD_hat+beta=P.                         (1)

The new source instead computes

    P=V+YI_hat+YD_hat+beta,
    N_P=P−(B−1)J.                                   (2)

It retains the paid product (B−1)J, deletes the private last G addition,
and reuses its operands for the P row. Add the subtraction N_P and one
multiplication of N_P into the old native unit product. Remove comparison
(1), retaining every other ordinary comparison.

For the coupled form let W_native denote its seven-factor product. The
new polynomial is exactly

    W_native*N_P*(1+sum_j residual_j^2)−1.           (3)

There are six remaining ordinary residuals: remainder, control, payload,
loader count, and the two prescribed native input comparisons. The
normalized uncoupled-unit form retains its two additional native
comparisons and is also supported. A same-cost all-SOS finalizer is emitted
for both forms. Every gate reaches the corresponding complete output.

At any zero of (3), the positive integer in parentheses must equal1,
every remaining ordinary residual vanishes, and every individual factor
is1 or−1. In particular

    P=(B−1)J+e, e in{−1,+1}.                         (4)

We do not infer that W_native=1 until e has been proved positive.

## 2. Positive ports and weak-repunit bounds

Before equations, all unhatted words are nonnegative and P>=3. Equation
(4) excludes J=0, since that would give P=±1. Thus J>=1. The positive
definition of P and nonnegative coefficient definition of V give

    J<=U<=V<P, W<P, each Z_p<P, YI<P, YD<P.          (5)

For the prime selections use p−2>=1. For the action words use their
positive hats in (2); no AND conclusion is assumed. Each selector and
each class-selector sum is at most J. Hence each class mask is at most
(B−1)J=P−e<=P+1. A mask is not yet assumed to fit one base-P lane.

The retained exact remainder comparison gives

    R+S=sum_(zero edges e)(p_e−2)E_e <= (pmax−2)J.

Since J<=(P+1)/(B−1), B−1>2(pmax−2) and P>=3, this proves R,S<P.
The same estimate with B−1>2(h−1) gives (h−1)J<P for the range mask.
All these estimates precede selector, remainder and radix typing.

There are L=edge_count+prime_class_count+5 prescribed lanes; L=48 for
U21. Let a be the least power of two at least L, and retain the actual
paid native scale Q=B*P^a (a=64 by default). The packed H and Z words
have coefficients below P. The packed M word has coefficients at most
P+1. Even at e=−1,

    0<=H,Z<P^L,
    0<=M<[(P+1)/(P−1)]P^L<=2P^L<Q.                (6)

Therefore the unpadded words are nonnegative and below Q. Carries inside
M have been allowed in the bound, not discarded. Native padded ports are
16H+12,16M+10,16Z+8, with positive native scale q0=16Q. The three other
native truth fields are supplied positive witnesses. These are legitimate
positive ports before any native semantic theorem is invoked.

## 3. Native power recovery without a presumed native product sign

This is the new dependency step. For clarity distinguish the native
packed index r, first Pell index n, main Pell index p, and history scale P.
All native source rows are exactly the parent's normalized strong rows.
The individual norm factors cannot be−1 modulo4; hence they are+1.
Normalized strong restoration therefore gives the full ordinary strong
condition by i_old=Delta*i, independently of the product sign.

Allow the native checksum Qc=q0−sum F_i to be either sign. Positivity,
the native packing and q0>=16 give exactly the weak bounds in
[native coupled units Sections2–4](native_binary_index_coupled_units.md):

    q0^3+q0^2+q0+1<=r<q0^4, r>=4369,
    X=q0*(r+bound_beta)>r,
    Y>=q0, XY>2r+3, Y(r−1)>2(2r+3).                (7)

Write the native index and linear units as Nk=epsilon and Nl=lambda.
The local strong-rank and signed-index arguments in those sections use
only the individual units, both ratio slacks, positive roots and (7).
They do not use Qc=epsilon*lambda until afterward. They give

    K=k−h_native*XY=r+epsilon,
    p=2K−lambda, n=K.

The upper ratio and Pell duplication exclude lambda=−1, again without
using a product-sign relation. Thus lambda=1. Put

    r'=K−1=r+epsilon−1.

Now r'>=4367, X>r', Y>=16 and p=2r'+1. The complete local fixed-minus
kernel equations hold at index r': k=r'+1+h_native*XY, the first and
main Pell norms, both strict ratio inequalities, positive main projection
quotient, full strong equation, and V_aux=jc−(2r'+1)=of−c. The first
root has the positive inverse supplied by its unit equation. No native
checksum or truth-field disjointness is part of this reconstructed kernel.

Apply only the exponent-recovery argument of
[binary selectors Section3](native_controller_binary_selector56.md).
It uses this kernel and the numerical bounds X>r'>=156, Y>=5. Its lower
ratio estimate gives Y>=X^(r'), hence a_native>X^(r'+1). The main
projection then gives X=2^(2r'+1) modulo4a_native+3, with both positive
representatives strictly smaller than that modulus. Therefore

    X=2^(2r'+1).                                    (8)

This conclusion uses no checksum equality, field partition, or AND lane
splitting. Since X is a positive integer multiple of q0=16Q, it forces
Q dyadic. As Q=B*P^a, both positive integer factors B and P are dyadic.

For the normalized uncoupled form the linear equation remains literal:
V_aux=jc−(2r+1). The same rank argument gives p=2r+1. If its exact
index comparison is retained, the same representative argument gives
n=r+1. Its weak checksum
still suffices for (7), so binary-selector Section3 gives (8) with r'=r.
This argument likewise never presumes a positive native product.

## 4. Recovering the repunit sign, then the complete AND relation

Write B=2^v and P=2^s. The fixed multiplier and h>=4 give B>=16, so
v>=4. Suppose e=−1 in (4). Then

    2^s = −1 modulo 2^v−1.

Reduce s modulo v to a remainder t in{0,...,v−1}. This would make
2^t+1 divisible by2^v−1. But

    0<2^t+1<=2^(v−1)+1<2^v−1

for v>=3. Thus the negative sign is impossible. We have e=1, and
P−1=(B−1)J with J>=1. The same reduction modulo2^v−1 forces v to
divide s, so P=B^T and J=1+B+...+B^(T−1), T>=1.

Now W_native=1 in (3), all its ordinary comparisons hold, and the full
inherited native coupled or uncoupled theorem applies to the legitimate
ports in (6). It yields H AND M=Z, including any required private native
normalization. Every outer supplied coordinate remains unchanged.

Alternatively, after e=1 the entire old sparse540 certificate is already
restored on the same coordinates: its recomputed old P equals (2), its
deleted global equality holds, and its unit product is1. This establishes
soundness into the complete parent without a further history proof. Its
typing, paid doubling-prefix/count equality, chronological payload and
control decoding give exactly the same ordinary-input relation.

Conversely, at every positive parent zero comparison (1) makes the new P
identical to the old P. Every retained source value is identical, N_P=1,
and (3) vanishes. These are identical positive zero sets, for arbitrary
positive program/input parameters; the usual E=3^e recipe supplies the
universal language slices. No parent witness is shifted or made signed.

## 5. Arithmetic, degree and exact checks

The certificate adds one multiplication overall: one deleted addition is
replaced by the new unit subtraction, and the unit-product multiplication
is added. One fewer ordinary residual removes one square and two additions
from the finalizer. Thus the complete polynomial saves two additions.

| Form | Certificate | Comparisons | Witnesses | Polynomial | Degree bound |
|---|---:|---:|---:|---:|---:|
|Normalized norm units|515=184M+331A|9|67|541=193M+348A|5345|
|Coupled index units|518=186M+332A|7|67|538=193M+345A|5091|

The computed P now has degree1 instead of2. The default factor bounds are
816,1900,442,65,1018,375,375,2, summing4993; the largest ordinary residual
bound is49. Hence the product degree is at most4993+2*49=5091. Its
same-cost SOS alternative has bound9986. These are propagated upper bounds
with the inherited guarded norm cancellation, not claims of exact degree.

The guard reconstructs the whole canonical sparse540 caller, checks the
private scale/bound rows and exports, preserves every native row and
requires complete topological closure. No historical rewrite helper is
reapplied to this altered outer scale. Metadata keeps the parent for
provenance; the emitted source and comparisons are authoritative.

The checker compares the complete new source against an independently
interpreted parent with an explicit intervention on its P register, then
evaluates both finalizers directly from the eight factors and six
residuals. It also checks exact complete-parent identities on the N_P=1
locus, allowing signed algebraic assignments without calling them positive
solutions. Complete shared/unshared packing identities, weak-repunit
carry bounds, dyadic sign/order exclusions, native index restoration and
actual outer accepted paths are separately tested. Wrong ordinary inputs
fail the paid count while retaining the other outer equalities. No finite
fixture materializes the full native Pell witnesses.

```sh
python3 residue_affine_sparse_scale538.py
```

The author writer and fresh replay pass. Ten emitted contexts cover five
tables and both native forms. There are640 complete finalizer/register
identities on320 assignments (160 signed),640 complete-parent identities
on the exact N_P=1 locus, and480 shared/unshared finalizer identities
(120 signed assignments). The locus tests include86 nonpositive algebraic
slacks. Separate checks cover350 weak-repunit packed bounds,175 at the
negative sign,1496 dyadic sign/order cases and16 native index reconstructions.
There are165 halted outer histories with892 rows across19 tables and149
wrong-input rejections. Five incompatible caller mutations are rejected.

Gibbs and Native independently reviewed the complete proof, source and
dependencies and each passed a fresh replay without findings. Both
specifically checked that native power recovery precedes the product-sign
and AND conclusions. Gibbs's separate executor checks512 complete
factor/residual/output identities on256 assignments (128 signed),512
complete-parent-locus outputs and384 actual-source weak-repunit fixtures;
192 use the negative sign,87 masks reach or exceed P, and383 scales are
nondyadic. Native independently expands the cancelled main norm and
matches32 degree/operation ledgers across16 contexts, including both
packing recipes and native forms. The default5091 product and9986 SOS
bounds agree. All local links resolve. These additional computations do
not materialize full native Pell tuples.

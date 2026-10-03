# A 179-operation complete binary-to-radix-four polynomial

The [complete129 recoder](native_binary_input_dilation129.md) has a
**179=86M+93A** single-polynomial successor, with **36 strictly positive
witnesses** and exact total degree **186**. Its positive projection is
still exactly

    z = sum_j bit_j(x) 4^j,       x,z>0.

The certificate has135 gates and15 comparisons. Every kernel, bound,
mask, common-exponent relation and quotient remains paid. The reduction
combines integer norm units, changes two positive root coordinates,
and removes thirteen coordinates whose positive values are already
computed by paid source gates. This is an explicit bijection of positive
solution sets after projection and coordinate change; it is not an
identity between the old and new polynomials.

The radix-sixteen [130 parent](native_binary_input_dilation130.md) similarly
gives **180=88M+92A**, with the same36 witnesses and degree240. The older
230/231-operation, degree40 sum-of-squares polynomials remain lower-degree
alternatives. None of these recoders alone certifies a variable tile
history or improves the separate universal75/88 bounds.

## 1. Integer units from the actual two kernels

Use either raw core, with its own positive coordinates and scale:

    X=wq0, Y=sq0, E=XY, V=XY^2,
    Delta=a^2+4a+3=(a+2)^2-1,
    T=i*c^2, U=j*c-(2r+1).

Here q0=q and r=J in the geometry core, while q0=16qP and r is the
packed four-field index in the AND core. The actual imported sources
both use T^2 in their auxiliary norm. Define

    N1=d^2-Delta*c^2,
    N3=T^2*(U^2-y^2)+y^2.                         (1)

The old comparisons are exactly N1=1 and N3=1. The latter is the Pell
form `(TU)^2-(T^2-1)y^2=1`. It is not the separate strong comparison
`T^2=Delta*(f^2-1)`. That full strong comparison is retained unchanged.

Both factors exclude -1 over all integer assignments, before any
positivity, Pell classification or bit typing is invoked:

* Delta is0 or3 modulo4. Hence N1 is respectively d^2 or d^2+c^2
  modulo4, and never3.
* T^2 is0 or1 modulo4. Hence N3 is respectively y^2 or U^2 modulo4,
  and never3.

The source already pays the additions `1+Delta*c^2` and `1-y^2` for
the old right sides. Replace those two gates by the subtraction and
addition in(1), using the already paid d^2 and T^2*(U^2-y^2). Thus
the two unit definitions in each core have exactly the old cost.
The source checks the literal T^2 coefficient and private consumers;
it does not import a sign assertion for a different auxiliary norm.

The default then makes one additional, cost-neutral change in each
core. Set K=Delta*(f^2-1), whose full value is already paid, and replace
only the coefficient of the auxiliary product:

    N3star=K*(U^2-y^2)+y^2.                       (1a)

This is a real change from the imported T^2 source, not an identity
away from its strong comparison. Its sign is independently safe:
Delta is0 or3 modulo4 and f^2-1 is0 or3, so K is0 or1 modulo4.
Consequently N3star is y^2 or U^2 modulo4 and cannot be -1. Both strong
comparisons `T^2=K` remain outside the unit product. They therefore
restore N3star=N3 on every zero. There is no assertion that an arbitrary
strong-equation residual has a prescribed sign.

The option `strong_auxiliary=False` retains the literal T^2 units.
It has the same operation and witness counts, with the larger degrees
recorded below. In the following formulas N3 means the chosen auxiliary
factor; with the default, restoring its old norm uses the retained
strong comparison explicitly.

There is one further factor:

    Qc = 16qP-(F0+F1+F2+F3).                       (2)

The old checksum is Qc=1. Its already paid `sum F+1` gate becomes
`16qP-sum F`, again at the same cost. No sign restriction is asserted
for Qc. With the four norm factors from(1), the equation

    N1_geo*N3_geo*N1_and*N3_and*Qc=1               (3)

forces every integer factor to be1: each is initially a unit +/-1;
the four independent modulo-four exclusions fix their signs, and
then Qc=1. This proves exact equivalence on the same integer tuples
for this first, unprojected option, together with the retained strong
comparisons in the default. It uses no raw-kernel theorem.

## 2. Two positive root gaps add two more sign-safe units

The triangular first equation in either core is

    (E^2+X)*(kY)^2=tau*(tau+1),
    equivalently V*(V+1)*k^2=tau*(tau+1).          (4)

Replace the supplied positive tau by a supplied positive g and define

    N0=g^2+4Vk*(g-k)
      =(2Vk+g)^2-4V*(V+1)*k^2.                   (5)

This factor is g^2 modulo4, so it cannot be -1 on any integer tuple.
The maps between positive zeros are explicit:

    g=2tau+1-2Vk,
    tau=Vk+(g-1)/2.                              (6)

For an old positive zero, `(2tau+1)^2=1+4V(V+1)k^2>(2Vk)^2`, so g>0.
Conversely N0=1 makes g odd, and V,k,g>0 make the second expression
in(6) a strictly positive integer satisfying(4). These maps are inverse.
No index, parity or population theorem is needed to prove this step.

The old six private gates for(4) cost4M+2A. The new six are

    g2=g*g; root_base=E*(kY); gap=g-k;
    cross=root_base*gap; four_cross=4*cross;
    N0=g2+four_cross.

They also cost4M+2A, including the multiplication by the fixed numeral4.
The source audits that every removed intermediate is private. The
remaining ratio equations and both positive ratio slacks are retained.

There are now six norm factors, N0,N1,N3 for each core, and the single
unrestricted factor Qc. Let their product be Zunit. Exactly as for(3),
`Zunit=1` forces all seven factors to be1. Restore the two old roots by
(6) before invoking either imported kernel theorem.

## 3. Thirteen positive definitions, with no free arithmetic

The default removes the following supplied coordinates. Each right side
is an existing paid source register; the rewrite aliases consumers and
removes the corresponding comparison. It neither adds a free arithmetic
operation nor deletes the gate computing that right side.

First set

    q=x+input_slack,
    P=(B-1)J+1.                                  (7)

Positive x and input_slack imply q>=2. For radix-four B=2q^2>=8;
for every generic width k>=4, B=2^(k-1)q^k>=8. Thus positive J makes
P>0 even before any equation. The option keeping P supplied still
projects q and uses the supplied P>0.

For each of the two cores set, in dependency order,

    s=2*odd_half+1,
    k=eta+zeta,
    c=kY+eta,
    a=E+Y,
    d=X+a*c+ga*(4a+3).                            (8)

The scaled X,Y and every value in(8) are strictly positive on all
positive supplied assignments. Their formulas are exactly the old
five defining comparisons, not additional assumptions about zero sets.

Finally, in the AND core set

    r=F0+q0*F1+q0^2*F2+q0^3*F3,  q0=16qP.       (9)

The first three fields remain supplied positive coordinates, and
`F3=16*Ahat-8>=8`. Thus(9) is positive before applying the AND theorem.
This pretyping positivity is essential: it is not inferred from a
desired Boolean interpretation of the fields.

Equations(7)--(9) eliminate2+10+1=13 witnesses and comparisons. A
topological sort makes the new dependencies explicit; it introduces no
copy gates or cycles. All remaining bounds, including X>r in each
kernel, J>B in geometry, both ratio slacks, the two full strong
comparisons, two auxiliary linear comparisons, masks and fold bounds
remain in the source.

Given a new positive zero, restore(7)--(9), use the unit signs to obtain
odd gaps, and apply(6). Every restored old witness is positive and every
old comparison holds. Conversely, an old positive zero has exactly the
computed values(7)--(9); its positive gaps from(6) give a new zero.
These maps are inverse. Consequently the complete recoder proofs apply
with their actual rawgeometry47 and prescribedAND64 domains, without
weakening a sign condition or invoking a kernel on a signed witness.

## 4. One integer-product polynomial and literal costs

Let R_1,...,R_h be the remaining nonunit comparison residuals, with
their usual paid subtractions. Use

    F = Zunit*(1+sum_i R_i^2)-1.                  (10)

Since `1+sum R_i^2` is a positive integer, F=0 forces that integer and
Zunit both to be1. Hence every R_i=0, followed by the unit and positive
restoration arguments above. The converse is immediate. This argument
does not assume Zunit is nonnegative away from zero.

For e=h+1 comparisons, finalizing(10) costs e multiplications and
2e-1 additions/subtractions, exactly3e-1 gates. It costs the same as
the complete sum of squares of those e comparisons. The source exposes
both finalizers; they have identical integer zero sets but different
polynomials and usually different degrees.

For the radix-four parent the exact alternatives are:

| Option | Certificate | Comparisons | Positive witnesses | Polynomial | M+A | Default product degree | Default SOS degree | T^2 product degree |
|---|---:|---:|---:|---:|---|---:|---:|---:|
|Four norm units and checksum; same coordinates|133|30|49|222|99M+123A|66|52|70|
|Also two positive first-root gaps|135|28|49|218|99M+119A|59|90|63|
|Also(8),(9) and computed q; P supplied|135|16|37|182|87M+95A|132|192|140|
|Also computed P: default|135|15|36|179|86M+93A|186|268|194|

The first row's SOS is the preferable degree52 version at the same222
operations. The latter rows prefer(10). These are upper bounds from
specific paid schedules, not optimality assertions.

Writing C for an actual compatible parent's certificate cost and e0 for
its comparison count, the default adds six product multiplications,
merges seven comparisons into one, and removes thirteen definitions.
Its certificate is C+6, its comparisons e0-19, and its final cost is
`C+6+3(e0-19)-1`. The root renamings do not change witness count.

For the [generic fixed-width recoder](gpcp_fixed_program_input_bridge.md),
let `ell(k)=floor(log2 k)+popcount(k)-1` be the length of its paid binary
power chain. Its default successor costs

    certificate134+ell(k), polynomial178+ell(k),
    (86+ell(k))M+92A, 15 comparisons,36 witnesses. (11)

For the complete framed GPCP boundary in that packet, including its six
additional framing/terminal gates and two comparisons, the result is
`190+ell(k)` polynomial operations,17 comparisons and37 witnesses.
At width4 these are142 certificate /192 polynomial operations. This
is only the same fully paid boundary predicate: the unbounded selected
tile history remains an explicit obligation.

## 5. Exact degree without using any zero-set relation

All degrees here concern the literal polynomials in their supplied
coordinates. No power-of-two fact or relation such as P=B^n is used.

For the default let v=k+2, where k is the bit-block width (k=2 for the
radix-four source). The two computed scales have degrees1 and v.
In the geometry core, the three unit degrees in source order
N1,N3star,N0 are12,18,8. In the AND core they are

    5v+7, 10v+8, 3v+5,

and Qc has degree v. Therefore

    deg Zunit=19v+58.                              (12)

For example, in a core with scale degree v, (8) gives degrees
`deg a=2v+2`, `deg c=v+2`, `deg d=3v+4`. In N1 the leading
`a^2*c^2` terms cancel after the explicit substitution for d; the next
term is `8*ga*a^2*c`, of degree5v+7 and nonzero. This is an ordinary
polynomial cancellation established from the source definition, not
use of a comparison. In the geometry core v=1 gives degree12.

In the AND auxiliary ordinate, the packed index has degree3v+1 and
dominates j*c. The default N3star has leading term `4*a^2*f^2*r^2`
and degree10v+8. The geometry ordinate instead has leading term j*c,
giving degree18. Keeping the T^2 coefficient gives respectively
`4*i^2*c^4*r^2` of degree10v+12 and degree22, four higher in each
core. Each N0 has leading expression `4*Vk*(g-k)` of the indicated
degree; it is a nonzero polynomial in independent supplied variables.

The largest remaining residual is the AND strong comparison. Its
T^2 term has degree4v+10, while its Delta*(f^2-1) term has degree4v+6.
All other residuals have smaller degree, including the surviving
index, X bound and auxiliary linear equations. Its square therefore
has a nonzero leading coefficient in the outer sum. Equations(10),(12)
give the exact degree

    27v+78 = 27k+132.                              (13)

Thus k=2 gives186 and k=4 gives240. The framed boundary has the same
degree: its new residuals have degree at most k, below4v+10.

With P supplied but the other definitions projected, the scales have
degrees1 and2. Zunit has degree96; the outer maximum is
`max(18,k+1)`, giving degree `96+2*max(18,k+1)`.
With only the root gaps changed the degrees are
`45+2*max(7,k+1)`. With no coordinate changes the product degree is
`26+2*max(20,k+1)`. For the T^2 option add8 to a projected product
degree and4 to an unprojected product degree. The alternative SOS
degree in each case is twice
the maximum of the unit-product and outer-residual degrees.

The checker evaluates exact weighted affine univariate polynomials for
each unit and residual. It chooses root-gap and raw-k weights that
cannot accidentally cancel g-k, checks the stated degree, and records
a hash of the nonzero leading coefficient. It does not expand the
unnecessarily large final product to infer its degree.

## 6. Source interface, identities and evidence

[The checker](native_binary_input_dilation_unit179.py) and
[compact receipt](native_binary_input_dilation_unit179.json) expose:

* `rewrite(old, core_prefixes, ...)`, accepting the actual compatible
  recoder or framed boundary DAG; the geometry and AND prefixes are
  explicit and the critical norm/definition gates are audited;
* `lift(packet, values)` and `project(packet, old_values, old_env)`;
* `polynomial_source(packet, sum_of_squares=False)`, plus the exact
  unit factors, removed comparisons and alias map in packet metadata.

Off zero, lifting a positive even g can produce a half-integral old
tau. That is intentional and limited to the unconditional rational
identity audit. For every such lift, with old residuals r, each new
factor is exactly `1+r_main`, `1+r_aux`, `1-4*r_first` or
`1-r_checksum` when the T^2 option is used. With the default coefficient,
the auxiliary factor is instead exactly

    1+r_aux-r_strong*(U^2-y^2).

The source checks this correction against the original parent DAG.
Removed defining residuals are identically zero;
the remaining residuals agree exactly. The complete new output is
the product of these explicit factors times `1+sum remaining r^2`,
minus1. On actual integer zeros each gap is odd, so the inverse map
returns strictly positive integer witnesses.

The deterministic receipt checks3,168 complete raw output identities
over positive and signed assignments at widths2,4,8,24, across all
four stages, both auxiliary coefficients and the framed boundary. It
also verifies640 modulo-four cases and128 independent positive
first-root Pell bijections. Thirty-two
recoder degree audits and one boundary degree audit use the actual
paid source. No full astronomical two-kernel zero is materialized;
completeness is the exact positive transport proved above and the
already established complete parent recoder theorem.

Normal execution compares the saved receipt; `--write` regenerates it.

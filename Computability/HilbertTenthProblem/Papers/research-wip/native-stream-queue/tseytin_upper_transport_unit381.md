# A typed upper boundary gives a381-operation universal polynomial

The complete [cross-offset C2 compiler383](tseytin_cross_offsets383.md)
has a successor costing **381=176M+205A**, with373 certificate operations,
three comparisons,62 positive witnesses, one fixed positive program parameter
and ordinary positive input. Its degree is **at most4717**. The
[literal source](tseytin_upper_transport_unit381.py) and
[receipt](tseytin_upper_transport_unit381.json) retain the complete paid source.

The change preserves the **full supplied positive zero set on every valid
recompiled program slice**, with every coordinate unchanged. It turns the
upper transport into an integer unit and uses the already recovered history
digits to exclude its negative sign. It is a direct application of the
[U9 upper-history unit argument](neary_woods_universal_history_units260.md#3-force-both-new-signs-and-reconstruct-a-parent-zero)
to the actual C2 source, with its different native sign dependencies checked
below. This is not an off-zero polynomial identity or an exact-degree claim.
The separate75-certificate/87-polynomial bounds remain unchanged.

## 1. Replace one private boundary addition

Let D=`height_slack`, B=65536D and P=(B−1)J+1. The old upper transport is

    B*NU+1=H_U+P*Ufinal.                              (1)

Its left side is the private register `U_lhs__151=U_update__150+1`.
The source deletes this register and replaces its one addition by

    T=U_rhs__155−U_update__150=H_U+P*Ufinal−B*NU.       (2)

Multiply T into the word-unit product and delete comparison(1). This adds
one certificate multiplication but removes one squared ordinary residual
from the finalizer: the complete saving is **two additions**. No coordinate,
fixed numeral, program encoding or input interface changes. The lower
transport and input query comparisons remain ordinary and paid.

The guards compare the complete canonical parent, then check the literal
boundary definitions, unique deleted comparison, lack of source consumers
or active exports of the deleted register, and both product interfaces.
The source is sorted and every gate reaches the final output.

|Global bound|Power products|Finalizer|Operations|M|A|Certificate|Comparisons|Degree bound|
|---|---|---|---:|---:|---:|---:|---:|---:|
|unit|merged|anchor|381|176|205|373|3|4717|
|unit|merged|SOS|381|176|205|373|3|9406|
|unit|separate|anchor|383|176|207|372|4|4757|
|unit|separate|SOS|383|176|207|372|4|9298|
|equality|merged|anchor|382|176|206|371|4|4715|
|equality|merged|SOS|382|176|206|371|4|9402|
|equality|separate|anchor|384|176|208|370|5|4755|
|equality|separate|SOS|384|176|208|370|5|9294|

All eight schedules have62 positive witnesses. The equality rows apply the
same change to the corresponding384 cross-offset parent; they do not alter
the global-bound treatment as part of this rewrite.

## 2. Recover native signs before either new boundary sign

At a zero, either finalizer forces all ordinary residuals to vanish and
each constrained product to be1. Thus T and every old factor are integer
units. In the global-unit form, write G for the old global factor and Sigma
for the sum of the ten positive history and selected-product ports. Then

    G=P−(Sigma+beta)=±1, beta>0,
    Sigma<=P, each port<P, J>=1 and B<=P.              (3)

The equality form has these same inequalities directly. They follow before
any transport or bit typing: Sigma>=10 excludes J=0 and P=1, while ten
positive ports make each strictly less than P even when Sigma=P.

These are precisely the hypotheses used in
[global-bound385, Sections1–3](tseytin_global_bound_unit385.md#1-the-source-change-and-its-initially-unknown-sign).
The exponent argument uses the retained paid query and the valid program's
residue exclusion; it uses neither history transport. Consequently its
product is+1 in the merged form; the separate form retains its product=1.

For the word core, the same weak scalar ports give four implicit positive
fields, sum q−1 and residues(1,4,2,8) modulo16. The four norms are+1 by
their independent modulo4 obstructions. The full strong norm, positive
ratio intervals and rank argument force the linear unit to+1 before
using any total-product sign. The remaining index unit would shift the
raw population argument from r to r−2. Its four low residues would then
be(15,4,2,8), with total population at least log2(q)+2, contradicting
the raw equality popcount(r−2)=log2(q). Thus the index unit is+1 too.

Every old local word factor is therefore+1 **independently of G and T**.
Do not use the final385 inference G=1 here: in the new source the product
at this stage only implies GT=1. In the equality form it already implies
T=1, but the following direct digit argument applies in either form.

## 3. Type the upper low digit, then restore the boundary

The independently restored native equations now give the prescribed AND.
As in [product-scale412, Section3](tseytin_product_scale412.md#3-type-the-product-factors-before-splitting-the-top-block),
the paid q=16B*P^34 makes B and P dyadic, and the exact repunit relation gives

    P=B^t, J=1+B+...+B^(t−1), t>=1.                  (4)

The physical, controller and range lanes split using the scalar bounds(3).
They recover one selected tile per row, the selected slope-class products,
and all H_U and H_V digits in[0,D). **No transport equality is used for
these lane and range conclusions.** In particular the least base-B digit
u0=H_U mod B satisfies0<=u0<D. This includes D=1 at this stage; it has
not been excluded by an endpoint assumption.

Since B divides P, equation(2) gives

    T=u0 modulo B.                                  (5)

The value T=−1 would require u0=B−1, impossible because D<B−1 for every
positive D and B=65536D. Therefore T=1. Equation(1) is restored exactly.
If enabled, the old global factor is now+1 from GT=1. Every old ordinary
comparison and product holds with the same supplied coordinates. The
complete383 or384 theorem then gives its accepted ordinary-input relation
on the unchanged valid program slice.

Conversely, every positive parent zero already satisfies(1), so its new T
is1 and all new product and ordinary conditions hold. Both implications
retain every coordinate, proving full positive-zero equality on the stated
slices. No positive-slack translation, native reconstruction or new
completeness witness is required. The usual later recovery of the literal
input, endpoints and full chronology belongs to the restored parent theorem;
none was assumed to prove(5).

The same sign order also works with an ordinary full strong equation: the
size and rank check in385 Section4 occurs before either transport. That
observation is available for future grouped sources; this packet emits
only the normalized strong schedules in the table.

## 4. Complete source corrections and degree accounting

Let W and E be the parent word and exponent products, S the sum of the
retained ordinary residual squares, and T the new factor. Put U=WE and
Splus=S in the merged form, or U=W and Splus=S+(E−1)² in the separate
form. The old upper residual is1−T. Thus the old and new anchor outputs are

    U[1+Splus+(T−1)²]−1, U*T*(1+Splus)−1.

Their difference is U(T−1)(Splus−T+2). The corresponding SOS difference is

    U²(T²−1)−2U(T−1)−(T−1)².

The checker verifies these exact full-output corrections and every retained
parent register on positive and signed assignments, including zero decoded
selectors. They explicitly distinguish this rewrite from an integer-polynomial
identity.

The new factor's propagated degree is3; the surviving query residual still
has degree bound7. The established guarded main-norm cancellations are
unchanged. In the merged global-unit anchor the old factor total4700 becomes
4703, so the bound is4703+14=4717. The SOS bound is2*4703=9406. The same
literal propagation gives every table entry. These are degree upper bounds,
with no expanded-degree or unrestricted-optimality claim.

The initial author replay passed256 complete retained-register maps
(128 signed),512 complete output corrections(256 signed),16 zero-selector
contexts, all eight degree/opcode/liveness ledgers and57 malformed callers.
Separate scalar checks cover1620 typed-residue sign exclusions and eight
genuine positive affine upper-history paths. Those fixtures are not complete
compiled Pell zeros; the general equivalence follows from Sections2–3.

Author writer47863 passed after adding strict Boolean checks before caching.
Gibbs's independent full proof/source/dependency review and fresh31413 passed
with no findings. His separate executor checked192 retained-register maps,
384 complete output corrections(192 signed), two symbolic finalizer identities,
all eight degree/opcode/domain/liveness ledgers and16 zero-selector contexts.
An independent affine interpreter checked48 histories using the actual24 tiles
(189 rows); separate boundary enumeration checked2814 sign exclusions and282
positive solutions. All five local links and whitespace passed. Native also
independently checked the pretransport sign order and initial source replay;
neither review treats finite outer histories as full native Pell zeros.

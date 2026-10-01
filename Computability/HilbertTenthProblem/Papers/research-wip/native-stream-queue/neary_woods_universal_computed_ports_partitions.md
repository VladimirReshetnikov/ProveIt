# Exact regrouping with the factored joined ports

The [computed-fields packet](neary_woods_universal_computed_ports275.md)
specializes selected earlier finalizers. This packet instead removes the
checksum **before** optimizing the groups. It searches every factor
partition of each of the sixteen inherited choices of strong treatment
and positive scale coordinates, then applies the exact six-addition
port factorization. The resulting complete frontier runs from **269
operations, degree at most3853,43 witnesses** to **279 operations,
degree at most608,44 witnesses**. It improves four intermediate degree
bounds over the mapped selected-family schedules:

| Factored operations | Unfactored operations | Previous mapped bound | New bound | Witnesses |
|---:|---:|---:|---:|---:|
| 275 | 281 | 1142 | 1094 | 44 |
| 276 | 282 | 1098 | 1048 | 44 |
| 277 | 283 | 764 | 734 | 44 |
| 278 | 284 | 734 | 706 | 44 |

All numbers concern the same complete U9 ordinary-input universal
relation on its inherited valid program slices. They are upper bounds
on polynomial degree. The search proves optimality only for the finite
family and propagated objective defined below. The separate 75-operation
certificate and 87-operation universal polynomial are unchanged.

## 1. The sixteen literal bases

For each native core independently, choose ordinary strong treatment or
its normalized strong treatment. Independently choose whether to absorb
its scale comparison into a positive scale coordinate. Thus there are
four strong subsets times four positive-scale subsets. Both cores always
retain the reviewed index and coupled-linear transformations. This is
the family from [positive-scale partitions](neary_woods_universal_positive_scale_partitions.md).

`input_base` builds one aggregate unit group on each such source, then
applies the existing loader-scale, positive mask-gap and duration-floor
rewrites. These are source transformations with their own literal row,
consumer and interface guards. The new `compute_fields` accepts only
the exact canonical source and public interfaces produced by that
builder. It performs the same three-field specialization as the 275
packet:

\[
 F_1=A-Z,\qquad F_2=B'-Z,\qquad
 F_0=q-A-F_2-1.
\]

Here \(A,B',Z,q\) are the joined padded native ports and scale. The two
input-port comparisons and three supplied field coordinates disappear;
the checksum factor becomes the literal integer one. One multiplication
in the aggregate product disappears. All other rows remain literal
parent rows. The native packed index still uses the original three
Horner multiplications and the computed fields.

The source checks the complete dependency closure of the two retained
outer comparisons and all four joined ports against the same closure
on the fully normalized/scaled base. It is identical for every strong
and scale choice, separately for each program interface. Thus the
untyped margins in the 275 proof apply unchanged. In its notation,
with history radix \(p\geq6\), high scale \(T=p^{11}\), low scale \(L\),
and low ports strictly between zero and \(L\), those margins are

\[
 H_h-Z_h\geq1,\qquad M_h-Z_h>1,\qquad
 T-H_h-M_h+Z_h\geq2.
\]

They imply \(F_1,F_2,F_0>0\) at every new zero before native typing.
The mask-scale and history global-bound comparisons used here remain
ordinary squared comparisons in every finalizer in this packet.

The specialized one-group base has \(45-s\) positive witnesses, where
\(s\in\{0,1,2\}\) is the number of absorbed native scale coordinates.
The number of remaining unit factors is \(10+h\), where \(h\) is the
number of normalized strong cores. The four-parameter interface uses
`program_E` as its duration bound. The five-parameter interface retains
the separate bound. Both have identical operation, witness and degree
ledgers, with the respective inherited valid-slice contracts.

## 2. Positive semantics of arbitrary grouping

Let the remaining integer unit factors be \(U_1,\ldots,U_n\), and the
ordinary comparison residuals be \(r_1,\ldots,r_m\). Partition all
factors into nonempty groups and write \(V_j\) for each group product.
The permitted finalizers are

\[
 \sum_i r_i^2+\sum_j(V_j-1)^2,
\]

or, choosing exactly one group \(a\),

\[
 V_a\left(1+\sum_i r_i^2+\sum_{j\ne a}(V_j-1)^2\right)-1.
\]

A zero of either finalizer has every \(r_i=0\) and every \(V_j=1\).
For the second form this follows because two integers, one of which is
a positive integer of the form \(1+\mathrm{SOS}\), multiply to one.
Consequently the aggregate factor product is one. The computed fields
are positive by the preceding outer margins. Adding those coordinates
therefore gives a positive zero of the checksum-one aggregate parent.
The complete parent theorem proves soundness for the ordinary input.

Conversely, an accepted input on a valid program slice has the canonical
parent extension in which all native unit factors are individually one.
The two independent five-auxiliary canonical rebuilds justify either
strong normalization choice. The inherited positive-scale inverse maps
justify either scale choice. Sufficiently long dyadic leading-zero
padding supplies the loader and duration inverse coordinates, and the
retained typed recoder supplies the positive mask gap. These are the
same padding and coordinate hypotheses as the preceding packets; the
claim does not extend to arbitrary program tuples.

At this canonical extension the checksum is one. Erasing the three
defined positive fields leaves every remaining factor one, so **every**
grouped finalizer vanishes. Alternatively, the inherited negative joint
checksum/index branch can first be normalized through the private
\(F_0\mapsto F_0-2\), bound-gap \(\mapsto\) bound-gap \(+2\) change;
the parent proof makes all factors one and preserves the outer data.
No new sign or rank lemma is required here.

This proves equality of the accepted ordinary-input relation across the
whole family. Within one fixed specialized base there is a stronger
statement: its checksum is identically one, and the inherited coupled
theorem forces both linear and index signs to be positive as well as
all norm signs. Thus every aggregate-product zero already has every
remaining factor equal to one. Arbitrary regrouping preserves the full
positive zero set of that fixed base. No equality between all supplied
positive tuples in different strong/scale bases is claimed.

The all-integer identity tested for field specialization is distinct
from grouping: it compares the one-group source before and after adding
the three computed coordinates, not two differently grouped polynomials.
The latter generally have different values away from their zero sets.

## 3. Exact finite optimization

For a fixed base, let \(C_0\) be the cost of the dependency closure of
its factors and ordinary comparisons, excluding the aggregate product.
With \(n\) factors, \(m\) ordinary comparisons and \(g\) groups, either
finalizer costs exactly

\[
 C_0+(n-g)+3(m+g)-1=C_0+n+3m-1+2g.
\]

Every multiplication by a literal numeral and every addition or
subtraction costs one. Grouping adds no witnesses. All producer gates
are required by the emitted output; the checker verifies full source
closure and counts literal opcodes.

Let \(d_i>0\) be the propagated factor-degree weights, and \(e\) the
largest propagated ordinary-residual degree. A group has weight equal
to the sum of its factor weights. The objective for SOS is twice the
largest of \(e\) and the group weights. For anchor \(a\), it is

\[
 d(G_a)+2\max\bigl(e,\max_{j\ne a}d(G_j)\bigr).
\]

The unchanged [subset-DP engine](neary_woods_universal_joint_and_coupled_partitions.md)
computes the least possible largest group weight on any mask with any
specified group count. It enumerates the group containing the least
set bit and recursively partitions the rest. It prunes only branches
which cannot strictly improve the current bound. This covers every
unordered partition. For an unsquared finalizer it additionally checks
every nonempty possible anchor subset and applies the same exact DP
to the complement. Therefore it obtains the exact minimum objective
for each group count on each of the sixteen bases.

There are ten, eleven, eleven and twelve factors for the four strong
subsets, independently of the scale subset: 176 optimized ledgers per
program interface, 352 total. The emitted schedule is checked against
the actual source degree propagation, including the parent's guarded
main-norm cancellation. Search metadata and the full schedules are in
the accompanying receipt.

Before the port factorization, the unrestricted cost/degree frontier is

| Operations | Degree upper bound | Witnesses |
|---:|---:|---:|
| 275 | 3853 | 43 |
| 276 | 3437 | 43 |
| 277 | 3391 | 43 |
| 278 | 2273 | 44 |
| 279 | 1505 | 44 |
| 280 | 1459 | 44 |
| 281 | 1094 | 44 |
| 282 | 1048 | 44 |
| 283 | 734 | 44 |
| 284 | 706 | 44 |
| 285 | 608 | 44 |

The new 281/282 schedules use two SOS groups, of weights
\((546,547)\) and \((524,523)\). The 283/284 schedules use three SOS
groups of weights \((364,367,362)\) and \((345,349,353)\). These are
regrouped after the checksum is absent, rather than images of the old
optimal groups.

The fixed-43-witness frontier is
\((275,3853),(276,3437),(277,3391),(278,2380),(280,1810),(282,1344)\).
The fixed-44-witness frontier is the unrestricted frontier from 278
through 285. The fixed-45-witness frontier is
\((281,2262),(282,1494),(283,1452),(284,1082),(285,1042),
(286,724),(287,706),(288,608)\).
These are exact witness strata, not an assertion that each stratum's
points are undominated when more witnesses are allowed.

The smallest objective in the full family is 608. Indeed, the joint
auxiliary factor has weight at least 304 when its strong norm is not
normalized, and then \(e\geq206\). If it is normalized its weight is
at least 708. A nonanchor occurrence forces at least twice its weight;
an anchor occurrence forces at least its weight plus \(2e\). Every
case is at least 608, and the displayed 285 schedule attains 608.
This is a lower bound on this propagated objective only, not on exact
polynomial degree, circuit complexity, other core transformations or
other finalizers.

## 4. Uniform exact factorization and the final frontier

Apply [factored ports269](neary_woods_universal_factored_ports269.md) to
each emitted schedule. The changed private subgraph is identical in all
sixteen bases and independent of the finalizer. It uses the identity

\[
 F_0+qF_1+q^2F_2+q^3Z
 =(q-1)\bigl[1+A+(q+1)(B'+(q-1)Z)\bigr],
\]

with the three computed field definitions, then folds the existing
\(A+1\) and loader \(\widehat A-1\) affine expressions. Its guards
check every erased producer and consumer. Exactly six additions
disappear, with no change to supplied coordinates, comparisons, unit
factors, group products or polynomial value on any integer assignment.
Each full source retains the same propagated degree dictionary. The
source verifies this on all352 optimized schedules and checks all their
remaining gates reach the output.

Consequently subtracting six from the cost is uniform across the
entire finite search family, not merely its displayed frontier. The
previous DP's optimality statements therefore transfer without another
optimization assumption. The final unrestricted frontier is:

| Operations | Degree upper bound | Witnesses |
|---:|---:|---:|
| 269 | 3853 | 43 |
| 270 | 3437 | 43 |
| 271 | 3391 | 43 |
| 272 | 2273 | 44 |
| 273 | 1505 | 44 |
| 274 | 1459 | 44 |
| 275 | 1094 | 44 |
| 276 | 1048 | 44 |
| 277 | 734 | 44 |
| 278 | 706 | 44 |
| 279 | 608 | 44 |

The factored witness strata likewise subtract six from every cost in
Section3. In particular the fixed43-witness frontier is
\((269,3853),(270,3437),(271,3391),(272,2380),(274,1810),(276,1344)\).
The fixed44-witness frontier is the displayed frontier from272 to279.
The fixed45-witness frontier runs from275/2262 through282/608; every
point and literal ledger is stored in the receipt. The minimum bound
remains608, now reached at279 operations.

This extends the independent269 packet's selected-family scope without
modifying that packet or its receipt. The named coefficient identity
preserves full polynomials; the regrouping and cross-base equivalence
statements retain their separate scopes from Section2.

## 5. Replay and scope of the evidence

Run `neary_woods_universal_computed_ports_partitions.py` to regenerate
the deterministic checks and compare the saved receipt; `--write`
regenerates it. `build(operations, merge_bound=..., witnesses=...)`
returns the unfactored frontier source. `build_factored` takes its
factored cost (default269); `build_base` exposes each fixed one-group
base. The previously frozen files remain unchanged.

The author writer checks all 352 optimized ledgers and 64 additional
nonoptimized grouped schedules. It executes 3,328 complete grouped
outputs, including 1,664 signed assignments, against a separately
assembled scalar finalizer, and checks another3,328 complete factored
outputs against that same scalar value. It also checks 1,024 complete three-field
lift identities, including 512 signed assignments, across all sixteen
bases and both program interfaces. The latter include deliberately
positive off-zero inputs with negative restored fields, so they do
not silently assert off-zero positivity. Five modified-source or
public-interface callers are rejected. Each displayed source is saved
with its output, supplied coordinate lists and a source digest.

These are algebraic/source fixtures and degree-bound audits, not
materialized full positive Pell zeros. The infinite positive theorem
is the argument in Sections 1–2 and the cited complete parent theorems.
Author receipt generation and the refreshed factored default replay pass.
Gibbs's independent full proof/source/fresh-default review passes without
findings. His separate executor and manual scalar finalizers checked256
field lifts (128 signed),512 grouped outputs (256 signed), and512
identical factored outputs (256 signed) across all32 base/interface
contexts, including a positive off-zero tuple with a negative restored
field. A separate restricted-growth Bell enumeration checked14,032
partitions on sixteen actual seven-factor subsets against the DP. All
four local links resolve. These independent fixtures retain the
algebraic/component scope described above.

The root's independent full proof/source review and fresh final replay
also pass. That review checks all canonical-base guards, the identical
outer dependency closures, positive grouping semantics within each base,
every DP pruning rule and anchor case, and the propagated-only degree
floor. It separately checks the uniform six-addition transfer, literal
factored ledgers, witness strata and source ancestry. The final source
and deterministic receipt are unchanged by these reviews.

# Sharing a repunit product gives the complete U9 compiler in 242 operations

Both complete U9 compiler interfaces now use **242 = 129M + 113A**
operations, with the same **43 positive witnesses**, ten fixed numeral
roles, and degree **at most 936**. They compute exactly the same
polynomials as the frozen 243-operation sources on identical supplied
coordinates. The separate universal 84-operation bound is unchanged.

The range and controller masks both contain a multiple of J(P+1).
Computing that product once removes one addition from the controller
mask while preserving the full mask values. No source equation,
selector condition, native typing premise or coordinate substitution
is needed for this saving.

## 1. Two mask identities

Use the actual frozen 243 source and abbreviate

    J = hist__J__7,
    P = hist__P__10,
    D = hist__height_slack,
    T = tree_mask_product = hist__P_product__9 * hist__G12.

The existing paid rows already provide P+1 and D-1 as
`hist__repunit_factor__50` and `hist__range_cell__75`. Keep them and T
unchanged. The parent mask cone is

    oldRangeRepunit = J*(D-1),
    RangeMask       = oldRangeRepunit*(P+1),
    tree_mask_sum   = J+T,
    oldTreeShift    = P*tree_mask_sum,
    ControllerMask  = J+oldTreeShift.                            (1)

Including T, this cone costs four multiplications and two additions.
Replace it with

    sharedRepunit  = J*(P+1),
    RangeMask      = sharedRepunit*(D-1),
    newTreeShift   = P*T,
    ControllerMask = sharedRepunit+newTreeShift.                 (2)

Including the unchanged T, this costs four multiplications and one
addition. Both exits are preserved over every commutative ring:

    (J*(D-1))*(P+1) = (J*(P+1))*(D-1),
    J+P*(J+T)      = J*(P+1)+P*T.                               (3)

Here T could be any ring element. In particular the argument does not
replace `hist__P_product__9` by P-1, impose the global unit equation,
or assume a particular sign of that equation. The equality holds
before every native or controller test.

In the saved child source, `hist__range_repunit__76` now computes
sharedRepunit. Its old internal meaning changes, which is permitted
because the complete consumer audit below supplies both unchanged
exits. No claim is made that the old and new internal products or shifts
are equal separately.

## 2. Exact source edit and complete consumer boundary

Delete the one row

    tree_mask_sum = hist__J__7 + tree_mask_product.

Edit these four existing rows:

| Row name | Child expression |
| --- | --- |
| `hist__range_repunit__76` | `hist__J__7 * hist__repunit_factor__50` |
| `hist__range_mask__77` | `hist__range_repunit__76 * hist__range_cell__75` |
| `tree_mask_shift` | `hist__P__10 * tree_mask_product` |
| `hist__controller_mask__55` | `hist__range_repunit__76 + tree_mask_shift` |

Every other row is a literally retained record. There is no new row,
new supplied port, changed numeral recipe or topological reorder.
P+1 already precedes the redefined product, and the shared product
already precedes its new controller consumer.

The parent has exactly these direct consumers:

| Parent node | Complete consumer list |
| --- | --- |
| `hist__repunit_factor__50` | `hist__range_mask__77` |
| `hist__range_cell__75` | `hist__range_repunit__76` |
| `hist__range_repunit__76` | `hist__range_mask__77` |
| `hist__range_mask__77` | `hist__range_mask_region__91` |
| `tree_mask_product` | `tree_mask_sum` |
| `tree_mask_sum` | `tree_mask_shift` |
| `tree_mask_shift` | `hist__controller_mask__55` |
| `hist__controller_mask__55` | `hist__controller_mask_region__90` |

In the child the shared product feeds exactly the range-mask and
controller-mask rows. The deleted sum has no remaining reference, and
T feeds just the edited shift. The P+1 and D-1 rows feed their swapped
multiplication roles. Both exits still have the same single downstream
consumer listed in the table. All these lists are checked in both
complete parent and child arrays.

Thus RangeMask and ControllerMask are the only outputs from the changed
cone into the retained graph, and (3) preserves both. All other retained
rows keep identical operands. Substitution in topological order proves
identity of the complete final polynomials, including the last charged
subtraction:

    F242(parameters,witnesses) = F243(parameters,witnesses).      (4)

The only source work here is an inert graph edit and consumer check.
The mathematical proof of (4) is the two handwritten identities (3);
no saved source array is symbolically expanded or evaluated.

## 3. Domains and complete compiler semantics

Every supplied coordinate, positive domain and fixed program recipe is
unchanged. Therefore (4) yields the identity bijection between the full
positive zero tuples, including on arbitrary supplied parameter values.
On valid U9 program slices the complete parent theorem gives the same
ordinary-input representation of every recursively enumerable set of
positive integers with four effective fixed program parameters and
43 positive existential witnesses. Its separate five-program-parameter
interface is retained as well.

The full paid loader, unbounded existential history, range conditions,
controller tests, native predicates and endpoints are still present.
The eight positive contributions to P are unchanged. Both full masks
are unchanged even before those tests, so the inherited signed-prefix,
dyadic and nested-carry arguments require no new premise. There is no
assertion that an accepting word or positive source zero exists on a
rejecting input.

The polynomial equality transfers the parent's degree bound at most
936; no exact degree is asserted, and no degrees are propagated through
saved arrays. This result does not change the separate universal84
construction or claim a minimum operation count.

## 4. Counts and fresh evidence

Each source has 238 literally retained records and four edited records.
The only deleted record is one addition, so each full source costs
242 = 129M + 113A. All rows, all supplied ports and all ten fixed numeral
roles remain live. The receipt contains both complete child arrays,
484 rows in total, with their exact topological order and source hashes.
Before the unchanged final subtraction, the certificate costs
**241 = 129M + 112A** followed by one comparison with the already paid
geometry discriminant. That comparison count is separate from the
complete polynomial count.

The initial static scan found no identical operation records in either
243 parent, even allowing operand exchange for addition or multiplication.
The saving instead uses the displayed distributive and associative
identities. The resulting child arrays likewise have no such duplicate
records. This scan is only literal graph metadata, not a lower bound
or an exhaustive search over arithmetic identities.

The original fresh helper authenticates the parent and its proof review,
checks all parent and child rows for shape, count, topology, unique
production, liveness, numeral roles and complete consumers, and emits
the two complete child sources. Its only separate arithmetic checks are
two independently handwritten four-variable ring cuts corresponding to
(3). The cut variable called D in that helper is an independent variable
representing the whole factor D-1 above; T is also independent. Their
common expansions are `DJ + DJP` and `J + JP + PT`, respectively. No
source record is an input to either handwritten cut calculation.

The new helper wrote its receipt and matched it in both normal and
optimized Python modes from `/`, all before freezing. No supplied,
archived, committed, predecessor or frozen helper was executed or
imported, including a modified copy. No source array was numerically or
symbolically evaluated, and no source degrees were computed. The
complete 243 proof and independent proof review were read inertly;
its earlier machine and native proofs are inherited at their existing
scope, not newly re-audited here.

No wrong or unproved claim arose or was silently discarded in this
draft. The frozen parents and their retained counterexamples remain
unchanged. Further saving or optimality is not asserted.

Evidence SHA256:

- Helper: `10a8435cb9f0eed19e613a5619e03ae419d7df8530d6c09a0cbf895951b94be6`.
- Receipt: `6cda9e3ba334115d44d43c41b10a3f2714b35bb7d21baa655d7cdd3fb2c471d0`.

The following dependencies are authenticated under
`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue`,
with identical same-name frozen `/tmp` bytes allowed before installation.
Byte authentication is distinct from the proof-read scope above.

| Dependency | SHA256 |
| --- | --- |
| `neary_woods_shared_size243_riemann.md` | `ace6c824a2ef1e0fddd32dcd30919a9e4b6fa2118d30705579322e1c2cc09586` |
| `neary_woods_shared_size243_riemann.json` | `db9673ba90ca965273a961f6bfb7c03f0e0a512ec0850c2841be3091bdcc3620` |
| `review_neary_woods_shared_size243_aristotle.md` | `c5a893ad9c09c7b2d35f25a68bf66fb611b0ed837799363dc338e9da7a7b6151` |

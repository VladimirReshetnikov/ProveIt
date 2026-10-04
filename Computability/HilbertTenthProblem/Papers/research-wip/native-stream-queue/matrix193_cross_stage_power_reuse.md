# Share powers and repunits across the complete matrix source

The four complete sources cost **1,534 / 1,531 / 1,531 / 1,528 operations**, saving **30 multiplications and 4 additions each** from the immediate [grouped-power parents](matrix193_grouped_power_composition.md). They have the same **145 / 144 / 144 / 143 positive witnesses** and exact degrees **35,587 / 53,347 / 53,347 / 71,107**. Every complete output polynomial is identical to its immediate parent on identical supplied coordinates, over every commutative ring.

The [fresh helper](matrix193_cross_stage_power_reuse.py) emits all four complete acyclic arrays in the [receipt](matrix193_cross_stage_power_reuse.json). It reads both frozen predecessor trios only as authenticated inert bytes/data. The established universal bound84 is unchanged.

## 1. Eleven products and two repunits

Write Q for the actual paid scale register, baseline `r108`. This is a cut in the existing input-bearing source, not an extra supplied coordinate. Baseline register names below are transported through the frozen entry-controller maps for the three chart variants.

| Target | New paid product | Exact exponent identity |
|---|---|---|
| r166 | r142 * r136 | 14 = 6 + 8 |
| r138 | r142 * r143 | 18 = 6 + 12 |
| r551 | r139 * r145 | 84 = 36 + 48 |
| r173 | r135 * cp282 | 140 = 4 + 136 |
| r897 | r134 * r173 | 142 = 2 + 140 |
| cp526 | r139 * cp317 | 186 = 36 + 150 |
| r191 | r148 * r187 | 194 = 96 + 98 |
| r793 | r187 * cp282 | 234 = 98 + 136 |
| r554 | r200 * r191 | 338 = 144 + 194 |
| r803 | r134 * r554 | 340 = 2 + 338 |
| r798 | r135 * r794 | 472 = 4 + 468 |

Each new target still costs one multiplication. Its operands are retained paid producers, with their dependencies moved earlier where necessary. In particular, the coefficient producer `cp282=Q^136` is now used by packing; its already-paid inputs are advanced with it. The helper expands the old target and both new operands as exact integer polynomials in Q, verifies each exponent identity, and checks the newly scheduled target again. This replaces whole private chains; it does not supply any power for free.

Let R_n(t)=1+t+...+t^(n−1). The existing paid registers also give

    r185 = R_49(Q²),    r154 = R_8(Q²),    r204 = Q+1.

The two remaining replacements are

    r772 = r185*r204 = R_98(Q),
    r777 = r154*r204 = R_16(Q).

These use the polynomial identity `(1+Q) R_n(Q²)=R_(2n)(Q)`. It holds also at Q=0,1 and over arbitrary commutative rings; there is no division or positivity assumption.

The eleven power replacements alone remove25 multiplication rows. The repunit replacements remove `r764..r771` (4M+4A) and `r776` (1M). All34 removed rows and their mapped counterparts are recorded literally in the receipt. Their sets are disjoint, and fresh backward liveness confirms that all34 disappear from the complete source. Exactly13 retained definitions change. Every other retained definition is literal.

## 2. Paid chronology and complete polynomial identity

New dependencies can point forward in the old listing, so simply replacing operands in the old order would not be a complete circuit. The helper first computes backward liveness from the actual output. It then traverses retained rows in their old order, recursively emitting unpaid dependencies before each consumer. An active-stack guard rejects cycles. A separate sequential audit requires each operand to be a literal integer, a supplied port, or an already emitted producer.

The helper verifies that all non-pure-Q rows retain their relative order. The rescheduling only advances needed pure-Q producers across those rows. All retained rows and every supplied port remain live. No extra arithmetic operation, variable, fixed coefficient, or inverse is introduced by moving a producer.

For the whole-source proof, interpret the two full arrays in a common formal expression table. Replace only the13 proved cuts by their exact polynomial tokens, with each token containing the formal expression of the **actual computed Q**. The complete expressions for Q agree. Every retained producer then has the same token in the parent and successor, as does the final output. This is a congruence induction proving

    F_successor = F_immediate_grouped_power_parent

on all supplied coordinates, not merely on valid histories or at selector nodes. The integer-polynomial identities used at the cuts are independently expanded from the emitted arithmetic rows.

The four coefficient outputs are separately expanded in full for every variant:16 words and2,704 integer coefficient entries agree exactly with their immediate parents. All553 coefficient rows survive; only `cp526` changes definition. Their component count remains553=305M+248A. The component is listed in the actual new execution order, including the advanced `cp282` producer.

All24 previously paid group additions and73 grouped-population producers remain literal. All63 native rows, all20/19/19/18 residual producers, and all62/59/59/56 finalizer rows remain literal. Their surrounding inputs are covered by the whole-source identity; this packet does not reprove the native compiler from unrelated samples.

## 3. Full ledgers and inherited theorem

| Variant | M | A | Total | Positive witnesses | Exact degree |
|---|---:|---:|---:|---:|---:|
| No controller chart |736|798|1,534|145|35,587|
| Flow |735|796|1,531|144|53,347|
| Population |735|796|1,531|144|53,347|
| Both |734|794|1,528|143|71,107|

The four arrays contain6,124 paid binary rows. Their ordinary input, positive-witness lists, eight fixed coefficient ports, illustrative fixed bindings, output register and137 distinct integer literals are unchanged. These totals are fresh counts of complete live arrays. The earlier25A population saving and24M coefficient saving are already in the immediate parents and are not counted again.

Entire polynomial equality on unchanged coordinates gives exactly the same positive integer zero tuples as each immediate parent. Thus the same natural ordinary input `x>=0` and the same valid fixed-program numeral recipe apply. The exact-degree conclusions for those valid specializations transfer through equality on identical variables. Fresh syntactic upper degrees are recorded separately:36,547 /54,785 /54,785 /73,023. This packet claims no new dense or leading-component degree computation.

The older comparison across IDLE elimination continues to preserve only the ordinary input. Reconstructing the reverse history there may choose different height, packed fields and native witnesses. Nothing here upgrades that inherited statement to a bijection on pre-IDLE witness tuples. The zero IDLE slot, controller and coordinate lanes, chronology constraints, and packing exponents remain the inherited ones.

This is an arithmetic successor, not a new accepted-history fixture, native Pell construction, optimality theorem, or universal polynomial below84. The source and receipt do not copy historical test results as fresh evidence.

## 4. Fresh checks and replay

The helper authenticates the full grouped-power composition trio and full entry-controller map trio. All six exact hashes are recorded in its source and receipt. It uses no predecessor imports or execution. The receipt binds itself to the fresh helper's bytes. Strict parsing rejects duplicate JSON keys and nonfinite constants; receipt comparison is recursively type-exact and all guards remain active under `python -O`.

Fresh checks cover the complete four arrays,52 local polynomial identities,16 entire coefficient words, all retained-register and final-output identities, interfaces, liveness, chronology and literal source boundaries. Another32 signed modular register comparisons over two primes are supplemental diagnostics; half use arbitrary signed values for all supplied ports and half use the illustrative fixed bindings. They are not substitutes for the exact identities.

```sh
reuse_wip=/absolute/path/to/native-stream-queue
python3 "$reuse_wip/matrix193_cross_stage_power_reuse.py" \
  --root "$reuse_wip" --expect "$reuse_wip/matrix193_cross_stage_power_reuse.json"
python3 -O "$reuse_wip/matrix193_cross_stage_power_reuse.py" \
  --root "$reuse_wip" --expect "$reuse_wip/matrix193_cross_stage_power_reuse.json"
```

The immediate grouped-power trio can instead be read from `--parent-root /absolute/parent/directory`; the default is `--root`. Generation uses mutually exclusive `--output`. No predecessor or repository files are modified.

Fresh generation and fresh normal/optimized exact receipt replays from `/` pass.

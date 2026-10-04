# Compose population grouping with paid coefficient powers

The four complete matrix constructions now cost **1,568 / 1,565 / 1,565 / 1,562 operations**, with **145 /144 /144 /143 positive witnesses** and unchanged exact degrees **35,587 /53,347 /53,347 /71,107**. This incorporates both newly proved edits:25 additions saved by [grouped population reuse](matrix193_grouped_population_reuse.md) and24 multiplications saved by [coefficient power reuse](matrix193_coefficient_power_reuse.md). The saves are counted from actual complete arrays, not merely added as headline numbers.

Each entire polynomial equals its immediate grouped-population parent on identical supplied coordinates. The established universal84 bound remains unchanged. The [fresh helper](matrix193_grouped_power_composition.py) emits all four arrays in the [receipt](matrix193_grouped_power_composition.json), reading frozen predecessor files only as authenticated inert data.

## 1. Literal composition and full identity

Use the grouped-population arrays as the immediate parents. The coefficient-power packet supplies nine mapped edits for each variant. For each edit, the helper authenticates the actual old target instruction, checks that both new operands are earlier paid packing registers outside the coefficient component, and freshly expands their integer polynomials in the actual packing scale Q. It verifies the old target, new target and both operand powers, including their exponent sum.

The nine exponents are54,78,30,136,150,102,162,66 and186. Their replacement products and exact24 deleted rows are given in the pinned coefficient-power companion. Here the full arrays are independently constructed by applying those products and recounting backward liveness. The24 newly dead rows must be exactly the same private coefficient multiplications as in that packet. No packing row disappears.

All73 grouped-population sum rows and all24 rescheduled group definitions remain literal. The commutative packing duplicate remains absent. Every other retained instruction is literal relative to the grouped parent. All553 retained coefficient rows agree literally with the coefficient-power packet. Thus the edits do compose without invalidating either set of paid operands.

For every variant, exact expression interning checks every retained register and final output. Each of the nine locally proved power cuts is bound to the actual computed Q, whose complete expression is compared between arrays. Hence

    F_composed=F_grouped

over every commutative ring on the same supplied inputs. A separate full expansion checks all16 coefficient words and2,704 integer coefficients. These checks establish full polynomial equality;32 signed modular full-register comparisons over two primes are supplemental diagnostics.

## 2. Complete accounting

| Variant | M | A | Total | Positive witnesses | Exact degree |
|---|---:|---:|---:|---:|---:|
| No controller chart |766|802|1,568|145|35,587|
| Flow |765|800|1,565|144|53,347|
| Population |765|800|1,565|144|53,347|
| Both |764|798|1,562|143|71,107|

The four complete arrays contain6,260 rows. All rows and supplied ports are live. Each coefficient component has553=305M+248A rows. Every source retains137 distinct integer literals and eight fixed coefficient ports. All63 native rows, all20/19/19/18 current residual positions and the complete62/59/59/56-row finalizers remain literal. Fresh syntactic degree upper bounds are recorded separately from the exact degrees.

The totals are49 gates below the earlier affine-plus-IDLE arrays, with the same multiplication/addition savings in each variant. The ordinary input, positive-witness lists, output ports and illustrative fixed bindings are identical to both edit branches.

## 3. Domain, degree and limits

Entire polynomial equality preserves every positive integer zero tuple of the immediate grouped parent in both directions. The same natural input x>=0 and valid fixed-program numeral recipe apply. The exact degree theorem for every valid fixed-program specialization transfers through equality on unchanged variables. This packet performs no new leading-component or dense full-degree computation.

The simulation comparison to ancestors before IDLE elimination still preserves only the ordinary input: its reverse construction may choose fresh history, height, packed fields and native witnesses. This composition does not turn that older theorem into a common-witness bijection. Controller slots, zero IDLE slot,128 controller lanes,340 coordinate lanes and packing exponents are unchanged.

No new accepting trajectory, native Pell tuple, diagnostic source, arithmetic lower bound or minimality theorem is claimed. The helper builds fresh ledgers, identities and evidence rather than copying predecessor test metadata.

## 4. Inert inputs and replay

The helper pins both predecessor trios and the entry-controller register-map receipt. Their programs are never imported or executed. The packet's JSON records all seven hashes and binds its freshly emitted receipt to its own source bytes.

```sh
composed_wip=/absolute/path/to/native-stream-queue
python3 "$composed_wip/matrix193_grouped_power_composition.py" \
  --root "$composed_wip" --expect "$composed_wip/matrix193_grouped_power_composition.json"
python3 -O "$composed_wip/matrix193_grouped_power_composition.py" \
  --root "$composed_wip" --expect "$composed_wip/matrix193_grouped_power_composition.json"
```

For predecessor trios in another directory, supply `--packet-root /absolute/packet/directory`; it defaults to `--root`. Generation uses mutually exclusive `--output`. Duplicate/nonfinite JSON is rejected, receipt comparison is recursively type-exact, and explicit guards stay active under optimized Python.

Fresh generation and fresh normal/optimized exact receipt replays from `/` pass. Frozen predecessor and repository files are unchanged by the helper.

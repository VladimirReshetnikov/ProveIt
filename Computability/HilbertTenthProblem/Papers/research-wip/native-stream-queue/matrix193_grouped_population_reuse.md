# Reuse selector groups in the matrix population sum

The four complete matrix sources cost **1,592 / 1,589 / 1,589 / 1,586 operations**, saving **25 additions per array** from the [affine-plus-IDLE parents](matrix193_idle_affine_reuse.md). The improvement shares existing work: 24 additions in disjoint selector groups and one duplicate packing sum. Every entire polynomial, supplied coordinate, positive zero tuple and exact degree agrees with its immediate parent. The universal84 bound is unchanged.

The [fresh helper](matrix193_grouped_population_reuse.py) emits all four actual-table arrays in the [receipt](matrix193_grouped_population_reuse.json). Frozen Python files are authenticated as bytes only; none is imported or executed.

## 1. Population sum from already needed selector groups

In the uncharted parent, the97 rows r7 through r103 compute the sum of98 positive edge hats. The only external consumer of this chain is r105=r103−98, the raw total population J. Separately, the24 addition rows r110 through r133 compute16 disjoint groups required by the X selector:

| Group heads | Group size | Hats represented | Additions already paid |
|---|---:|---:|---:|
| r111, r113, r115, r117, r119, r121 |3|18|12|
| r122 through r130 |2|18|9|
| r133 |4|4|3|
| Total | |40|24|

Move those same24 definitions before the population sum. They depend only on edge hats9 through97, which are already supplied in all four variants. Replace the97-addition population chain by a sum of the16 group heads and the58 remaining individual hats. These74 terms need73 additions, saving24. Retain the final name r103 so all subsequent consumers stay connected to the same value.

The helper derives each group's support by exact integer linear expansion, verifies disjointness, and proves that the new sum and old sum both have coefficient1 on exactly the same98 formal hats. It authenticates the private chain boundary and all literal group definitions from the pinned parent. The groups remain paid; their rows are only rescheduled. No hat or group is newly supplied, and the controller charts' computed LOAD/SWITCH hats are used as their actual earlier values.

## 2. One commutative duplicate

The parent also computes both

    r140=1+r139,       r159=r139+1.

Their values agree over every commutative ring. Retain whichever producer is earlier in the actual source order and redirect the later one's consumers to it. In the uncharted array r140 is earlier; in the three chart arrays the mapped r159 is earlier. Deleting the later producer saves one additional addition. Choosing the earlier producer is necessary for the reordered chart sources to remain topological.

These two changes touch no coefficient component definition. All577=329M+248A coefficient rows remain literal.

## 3. Full source identity and accounting

The helper checks every other parent definition literally, allowing only the proved duplicate alias. It interprets both entire arrays with exact expression interning: addition and multiplication are commutative, and the population-sum cut is justified by the separate98-variable linear identity. The cut token binds all98 actual input values, including computed hats in the chart variants. Thus equality is not inferred merely from a shared register name. Every retained register and final output agrees.

| Variant | M | A | Total | Positive witnesses | Exact degree |
|---|---:|---:|---:|---:|---:|
| No controller chart |790|802|1,592|145|35,587|
| Flow |789|800|1,589|144|53,347|
| Population |789|800|1,589|144|53,347|
| Both |788|798|1,586|143|71,107|

The complete emitted arrays contain6,356 rows. Fresh topology and backward liveness checks require every paid row and every supplied port to be live. The eight fixed coefficient ports and137 distinct integer literals are unchanged. All63 native rows, every current residual, and each complete62/59/59/56-row finalizer remain literal. All16 entire coefficient polynomials are independently expanded in the actual paid Q and compared with the parent's2,704 coefficients.

Thirty-two signed modular assignments over two primes additionally compare every common register and final output. Half use the illustrative fixed coefficient bindings and half vary every supplied value. These are supplementary off-zero checks; the exact population identity and complete expression proof establish the polynomial identity.

## 4. Domain and degree scope

For each variant, F_child=F_parent on identical supplied coordinates over every commutative ring. In particular, all positive integer zero tuples and the ordinary input projection are identical to the immediate affine-plus-IDLE parent. The valid fixed-program numeral recipe,98 retained edge hats,99-slot controller numbering with a zero IDLE slot,128 controller lanes,340 coordinate lanes and all packing exponents are unchanged.

Uniform exact degrees transfer from the pinned immediate parent by full polynomial identity on the same variables, for every valid fixed-program specialization. No new leading-component computation is claimed. Fresh syntactic upper bounds, recorded separately, remain36,547 /54,785 /54,785 /73,023.

Comparison with an ancestor before IDLE elimination still has only the ordinary-input scope proved there: constructing a reverse simulation may choose a new history, height and native witnesses. This packet does not strengthen that statement to a common-witness bijection. It adds no native Pell tuple, accepting trajectory, diagnostic array or minimality claim.

## 5. Authenticated inputs and replay

| Inert dependency | SHA-256 |
|---|---|
| `matrix193_idle_affine_reuse.py` | `a2dcb0e17ede95c182af4c1f4895b8551eb3786a376da3d081439baf8b896d72` |
| `matrix193_idle_affine_reuse.json` | `84a1d55889c8adff1c20b7c0e4bf3e69055ed6aefd9b0eea5065b3b082ba9dd5` |
| `matrix193_idle_affine_reuse.md` | `d8f63c7e3957564a0b2d2d39080cddc7a93f8920ed6c05bc25ce48e5cbd44f63` |
| `matrix193_entry_controller_charts.json` | `d5b4490017c9b4ad46d700d8999ad1f5dedde789dd19a3d5f7b5375a1468a571` |

The chart receipt is used only for its authenticated register maps. The current parent supplies each actual full source and interface. Fresh metadata records the edits and evidence without copying old test claims.

```sh
grouped_wip=/absolute/path/to/native-stream-queue
python3 "$grouped_wip/matrix193_grouped_population_reuse.py" \
  --root "$grouped_wip" --expect "$grouped_wip/matrix193_grouped_population_reuse.json"
python3 -O "$grouped_wip/matrix193_grouped_population_reuse.py" \
  --root "$grouped_wip" --expect "$grouped_wip/matrix193_grouped_population_reuse.json"
```

Generation uses mutually exclusive `--output`. Duplicate keys and nonfinite JSON are rejected, receipt equality is recursively type-exact, and explicit checks remain active with optimized Python. Fresh normal and optimized exact replays from `/` pass. No frozen predecessor or repository file is changed by the helper.

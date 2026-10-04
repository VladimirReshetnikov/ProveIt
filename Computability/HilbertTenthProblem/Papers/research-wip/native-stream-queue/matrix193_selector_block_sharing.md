# Share contiguous selector blocks between X and Y

The four complete matrix sources cost **1,418 /1,415 /1,415 /1,412 operations**, saving **46 multiplications and46 additions each** from the [terminal-power parents](matrix193_terminal_power_composition.md). They retain **141 /140 /140 /139 positive witnesses** and exact degrees **35,587 /53,345 /53,347 /71,105**. Every entire polynomial is unchanged on identical supplied coordinates, over every commutative ring.

The saving comes from shared interior blocks of two selector words. It changes neither the fixed coefficient polynomials nor their553-row component. The [fresh standalone helper](matrix193_selector_block_sharing.py) emits all four full arrays and the exact certificates in the [receipt](matrix193_selector_block_sharing.json). Frozen programs are read only as authenticated inert bytes/data. The established universal84 bound remains unchanged.

## 1. The two existing words

Let Q be the actual paid packing scale and t=Q². The positive-hat packing already computes two words

    X(t)=sum_(j=0..71) x_j t^j,
    Y(t)=sum_(j=0..96) y_j t^j.

The x_j are the72 paid sums for the distinct K classes. The y_j are the96 individual tile hats followed by the LOAD hat. The ordinary controller word is a separate polynomial and remains unchanged. The multiplicity corrections and duplication factors converting these raw words to physical selectors also remain unchanged.

In the baseline literal source, the two raw outputs are `r346` and `r540`, with Horner base `r134=Q²`. The helper extracts every coefficient by traversing the actual multiplication/addition chains. It authenticates lengths72 and97, exactly142 and192 old rows, disjoint old cones, leaves outside both cones, and the fact that only the two outputs have consumers outside their respective replaced cones. Frozen controller maps transport the names for the other variants.

The two lists contain these identical contiguous runs. Indices are zero-based and start at the lowest degree; edge numbers refer to `edge_hat` names before applying the controller map.

| X start | Y start | Length | Shared coefficients |
|---:|---:|---:|---|
|0|0|7|hats2 through8|
|10|10|3|hats12 through14|
|13|16|12|hats18 through29|
|28|40|3|hats42 through44|
|34|46|3|hats48 through50|
|37|52|12|hats54 through65|
|52|67|3|hats69 through71|
|58|73|3|hats75 through77|
|61|79|9|hats81 through89|

The helper checks all36 mapped run occurrences across the four variants and verifies disjoint intervals within each word. The nine runs contain55 coefficient positions in each word. These are explicit reusable intervals; no global optimality of the chosen partition is claimed.

This differs from the earlier hat-packing rewrite, which removed individual hat shifts and paid the fixed multiplicity corrections. It also differs from the prior scalar coefficient and power rewrites. Here two variable selector words share their identical interior polynomials even though their complete Horner prefixes differ.

## 2. Exact arithmetic and paid joins

For a low-to-high list A of length k, define H(A;t)=sum A_j t^j. The construction computes each listed shared run once by ordinary Horner evaluation. All remaining positions are singleton blocks whose values are already-paid selector coefficients. It then assembles each word from its high end, using

    H(A concatenated with B;t)=H(A;t)+t^len(A) H(B;t).

Every join costs one multiplication and one addition. The only block lengths are1,3,7,9 and12. Their scale factors are existing paid registers:

| Block length | Scale | Baseline paid register |
|---:|---|---|
|1|Q²|r134|
|3|Q^6|r142|
|7|Q^14|r166|
|9|Q^18|r138|
|12|Q^24|r144|

Fresh univariate expansion authenticates all these register values. There are **no new power gates**. Each multiplication by one of these registers remains explicitly paid at every use.

The X partition has26 blocks and the Y partition51. Evaluating the nine shared runs costs

    2*sum(length−1)=2*(55−9)=92 operations.

Joining the two partitions costs2*(25+50)=150 operations. The new component therefore has242=121M+121A rows, replacing334=167M+167A. All242 rows are present in each emitted full array and live. No scalar multiplication, join or free coefficient combination is omitted.

The complete component is inserted at the first old cone position. Sequential validation checks that every selector leaf and scale register is already paid at use. Every surrounding instruction retains its literal definition and relative order. No chronology or packed-field layout is altered.

## 3. Full polynomial identity

First regard the selector leaves and Q as independent formal variables. The helper expands both old private Horner cones and the new component as sparse integer polynomials, linear in the selector leaves and polynomial in Q. For each entire word the old and new expansions equal its complete coefficient list, including all72 or97 positions. The local proof is not inferred from numerical evaluations.

For the whole-source proof, the two exact word identities are substituted into a common formal interpretation of both complete arrays. Each cut token includes the complete expression for the actual Q and the complete expressions of every selector leaf occurring in that word. This includes grouped hats and controller-chart values; they are not treated as extra supplied coordinates. Every retained parent register and the final output has the same resulting expression token. Consequently

    F_shared=F_immediate_terminal_power_parent

over every commutative ring, on identical supplied coordinates. The two substitutions are valid whether or not the selectors satisfy typing constraints, whether or not Q is positive, and whether or not fixed coefficient assignments define a program.

All553 fixed-coefficient rows remain literal. Their sixteen full output polynomials and2,704 coefficients are independently expanded again. All63 native rows,97 paid group/population rows, current residual producers and finalizer rows remain literal. Parent and child finalizers are each explicitly traced from the output through the native multiplier, one-plus-SOS, complete sum tree and exactly one square of every residual; no contiguous-suffix assumption is used.

## 4. Complete counts and scope

| Variant | M | A | Total | Positive witnesses | Exact degree |
|---|---:|---:|---:|---:|---:|
| No controller chart |686|732|1,418|141|35,587|
| Flow |685|730|1,415|140|53,345|
| Population |685|730|1,415|140|53,347|
| Both |684|728|1,412|139|71,105|

The four complete arrays contain5,660 paid rows. All rows and supplied ports remain live. The same natural ordinary input, positive-witness lists, eight fixed coefficient ports,137 distinct integer literals, illustrative fixed bindings and output registers are retained. Fresh ledgers count every complete emitted array; earlier arithmetic savings are already in the immediate parents and are not counted again.

Whole-polynomial equality preserves exactly the positive integer zero tuples of each immediate parent. It also transfers the parent's exact-degree theorem on unchanged variables for every valid fixed-program specialization. No new dense or leading-component degree computation is claimed. The same valid fixed-program numeral recipe applies to the ordinary-input language theorem.

Older comparisons across terminal-carry and IDLE charts continue to preserve only the ordinary input. This exact rewrite does not strengthen those earlier theorems into common-witness bijections. There is no new accepted-history fixture, native Pell tuple, minimality theorem or improved universal84 bound in this packet.

## 5. Fresh evidence and replay

The helper pins the complete terminal-power trio and complete entry-controller map trio, with all six hashes recorded in source and receipt. The receipt is bound to its fresh helper's bytes. Duplicate/nonfinite JSON is rejected, receipt equality is recursively type-exact, and all explicit guards remain active under optimized Python. No frozen helper is imported or executed.

Fresh checks cover all four complete arrays, eight entire selector-polynomial identities, the mapped shared runs and paid powers, all fixed coefficient words, all-ring whole-source identities, topology/liveness, interfaces and eight finalizer traces. Another32 signed modular comparisons over two primes check every retained parent register and final output. Half use arbitrary signed values for all supplied ports and half use the illustrative fixed bindings. These diagnostics supplement the exact identities and do not claim accepting zeros or inherited giant-fixture replay.

```sh
selector_wip=/absolute/path/to/native-stream-queue
python3 "$selector_wip/matrix193_selector_block_sharing.py" \
  --root "$selector_wip" --expect "$selector_wip/matrix193_selector_block_sharing.json"
python3 -O "$selector_wip/matrix193_selector_block_sharing.py" \
  --root "$selector_wip" --expect "$selector_wip/matrix193_selector_block_sharing.json"
```

For a terminal-power trio in a separate directory, add `--parent-root /absolute/parent/directory`; it defaults to `--root`. Generation uses mutually exclusive `--output`. No frozen predecessor or repository file is modified.

Fresh generation and fresh normal/optimized exact receipt replays from `/` pass.

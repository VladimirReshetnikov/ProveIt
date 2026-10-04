# Reuse paid packing powers in the matrix coefficient component

Nine exact power refactorings save **24 multiplications** in each of the four complete [affine+IDLE-free sources](matrix193_idle_affine_reuse.md). The resulting counts are **1,593 / 1,590 / 1,590 / 1,587 operations**. The fixed coefficient component falls from577 to **553=305M+248A** rows. Positive witness counts remain145/144/144/143, and exact degrees remain35,587/53,347/53,347/71,107.

Every complete polynomial is unchanged on the identical supplied interface. All packing instructions remain literal; this packet does not incorporate a separate packing-sum or commutative-reuse change. The established universal84 bound is unchanged.

The [fresh standalone helper](matrix193_coefficient_power_reuse.py) emits all four full arrays in its [receipt](matrix193_coefficient_power_reuse.json). It reads frozen predecessors only as authenticated inert bytes, text and JSON. None of their programs is imported or executed.

## 1. Nine actual paid power identities

Use Q for the packing scale already computed by the complete source. The baseline coefficient component constructs several powers through private multiplication chains, even though suitable lower powers have already been paid in the packing prefix. Replace the final instruction of each listed chain by one product of earlier packing registers:

| Coefficient output | Exact power | New paid product | Operand exponents | Old chain cost | Saved M |
|---|---:|---|---|---:|---:|
| cp42 | Q^54 | r138*r139 |18+36|4|3|
| cp117 | Q^78 | r142*r161 |6+72|4|3|
| cp119 | Q^30 | r138*r143 |18+12|2|1|
| cp282 | Q^136 | r161*r783 |72+64|2|1|
| cp317 | Q^150 | r142*r200 |6+144|4|3|
| cp326 | Q^102 | r142*r148 |6+96|4|3|
| cp344 | Q^162 | r138*r200 |18+144|4|3|
| cp383 | Q^66 | r138*r145 |18+48|2|1|
| cp526 | Q^186 | r138*r552 |18+168|7|6|

The old chains have33 multiplications in total. Their nine retained endpoints still cost nine multiplications. The intermediate24 multiplications become dead and are removed:

    cp39..cp41; cp114..cp116; cp118; cp281;
    cp314..cp316; cp323..cp325; cp341..cp343; cp382;
    cp520..cp525.

Every removed row belongs to the coefficient component. No packing producer is deleted or changed. Every replacement operand is an earlier, already live packing register outside the component. In particular, this is a paid reuse statement, not free exponentiation or a new supplied-power interface.

For the three controller charts, the helper takes all producer names from the pinned [entry-controller maps](matrix193_entry_controller_charts.md), with the identity map for the uncharted source. It then checks the exact powers in the actual mapped parent arrays. No row number or anticipated count is used to infer the identities.

## 2. Exact complete polynomial identity

The helper expands the pure-Q subcircuits as integer univariate polynomials. For every variant and each of the nine edits, it verifies the old target, both actual paid operand powers, their exponent sum, and the new target. These are36 exact identities of the form

    Q^(a+b)=Q^a*Q^b.                                (1)

They hold over every commutative ring, without a positivity, dyadic-radix or nonzero-Q condition. Substituting the actual computed Q is therefore valid on every supplied tuple.

All nine edits are composed before liveness is recounted. Backward traversal of the complete output finds exactly the24 removed coefficient rows and retains every supplied port. The helper verifies that all other retained instructions are literal copies of the immediate parent.

A separate expression interpretation proves the complete identity. At each of the nine outputs it uses a token containing both the proved exponent and the **actual paid Q expression**. The parent and child Q values are checked equal, and every retained paid register and final output agree. Thus, for each variant v,

    F_new,v=F_idle_affine,v                           (2)

on identical ordinary input, fixed coefficient ports and supplied witness coordinates. There are no unchanged-name assumptions standing in for input equality at these cuts.

As a separate check, all four full coefficient words in each parent and child are freshly expanded and compared with the pinned effective coefficient lists. All **16 polynomials / 2,704 coefficient entries** agree. The X words retain degree143 and144 coefficients each; the Y words retain degree193 and194 coefficients each. The coefficient evaluations are complete paid source subgraphs.

All63 native rows, every retained residual position and the entire current finalizer are checked literally unchanged. No native constraint or final truth operation is removed.

## 3. Complete costs and retained scope

| Variant | M | A | Total | Positive witnesses | Outer residuals | Exact degree |
|---|---:|---:|---:|---:|---:|---:|
| No controller chart |766|827|1,593|145|20|35,587|
| Flow |765|825|1,590|144|19|53,347|
| Population |765|825|1,590|144|19|53,347|
| Both |764|823|1,587|143|18|71,107|

The four arrays contain **6,360 live rows**. All counts are derived from those complete emitted arrays. Every supplied port remains live, with the same eight fixed coefficient ports and137 distinct integer literals per array. The finalizer lengths remain62/59/59/56. Each553-row coefficient component has305 multiplications and248 additions/subtractions.

Because (2) is full polynomial equality on identical variables, every positive-integer zero tuple of the immediate parent is preserved in both directions. The same natural ordinary input x>=0 and valid fixed-program numeral recipe apply. No new height, witness reconstruction, accepting history or native extension is needed for this edit.

The relation to ancestors that still include optional IDLE retains the inherited **ordinary-input projection** scope. Their reverse construction may change the history positions, height, packed fields and native witnesses. This packet does not upgrade that theorem to a common-witness bijection. The fixed99-slot controller numbering, zero IDLE slot,128-lane controller region and340 selected-coordinate lanes remain unchanged.

The exact degrees in the table transfer through (2) from the immediate parents for every valid fixed-program specialization. This does not rely on a guessed syntactic degree or on substituting into only a leading term. The newly recounted syntactic upper bounds are recorded separately. No dense degree expansion or fresh native degree proof is claimed.

## 4. Evidence and boundaries

Fresh evidence comprises the four complete arrays and ledgers;36 exact local power identities; all16 full coefficient-polynomial comparisons; full expression identities; topology and backward liveness; and the literal native/residual/finalizer checks. Thirty-two supplemental signed assignments over two prime fields compare every retained register and output. Half use the illustrative fixed coefficient binding and half vary every supplied value. Those evaluations are off-zero arithmetic diagnostics, not accepting-trajectory fixtures.

A bounded scratch search suggested the nine products. This report promotes the exact edits, not an exhaustive search or a minimality theorem. No diagnostic array, giant outer history or native Pell tuple is newly materialized or replayed. No frozen predecessor or repository file is modified.

## 5. Inert provenance and replay

| Dependency | SHA-256 |
|---|---|
| `matrix193_idle_affine_reuse.py` | `a2dcb0e17ede95c182af4c1f4895b8551eb3786a376da3d081439baf8b896d72` |
| `matrix193_idle_affine_reuse.json` | `84a1d55889c8adff1c20b7c0e4bf3e69055ed6aefd9b0eea5065b3b082ba9dd5` |
| `matrix193_idle_affine_reuse.md` | `d8f63c7e3957564a0b2d2d39080cddc7a93f8920ed6c05bc25ce48e5cbd44f63` |
| `matrix193_entry_controller_charts.py` | `7c1e55ca1396958f234c2caf6c117702c4d69537cefcad51089498cb1e58f2bf` |
| `matrix193_entry_controller_charts.json` | `d5b4490017c9b4ad46d700d8999ad1f5dedde789dd19a3d5f7b5375a1468a571` |
| `matrix193_entry_controller_charts.md` | `27245d944d03b1d31ad79470dfd5625798834b7a47c1a03dee319f198214d122` |

After installation:

```sh
power_reuse_wip=/absolute/path/to/native-stream-queue
python3 "$power_reuse_wip/matrix193_coefficient_power_reuse.py" \
  --root "$power_reuse_wip" --expect "$power_reuse_wip/matrix193_coefficient_power_reuse.json"
python3 -O "$power_reuse_wip/matrix193_coefficient_power_reuse.py" \
  --root "$power_reuse_wip" --expect "$power_reuse_wip/matrix193_coefficient_power_reuse.json"
```

If the immediate parent trio is in a separate directory, add `--parent-root /absolute/parent/directory`; it otherwise defaults to `--root`. Generation uses mutually exclusive `--output`. Duplicate/nonfinite JSON is rejected, receipt equality is recursive and type-exact, and all explicit proof checks remain active under optimized Python.

Fresh generation and fresh normal and `-O` exact receipt replays from `/` pass.

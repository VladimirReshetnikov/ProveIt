# Compose paid affine reuse with the four IDLE-free matrix sources

The four complete actual-table sources now cost **1,617 / 1,614 / 1,614 / 1,611 operations**, with **145 / 144 / 144 / 143 positive witnesses**. Each saves one addition from its frozen [IDLE-free parent](matrix193_idle_free_scout.md) by reusing an affine value already paid in the packing prefix. Every complete polynomial and every supplied coordinate is unchanged relative to that immediate parent. Exact degrees remain **35,587 / 53,347 / 53,347 / 71,107**.

This composes the frozen [one-gate affine edit](matrix193_affine_reuse_scout.md) into all four IDLE-free arrays, including the three [controller charts](matrix193_entry_controller_charts.md). It does not remove another witness or change the instruction grammar. The established universal84 bound is unchanged.

The [fresh helper](matrix193_idle_affine_reuse.py) emits all four complete arrays in the [receipt](matrix193_idle_affine_reuse.json). Frozen predecessors are authenticated and read only as inert bytes, text and JSON; none is imported or executed.

## 1. The same paid identity in four literal sources

In the uncharted source, the existing packing prefix and coefficient rows are

    r181 = r144 + 1;
    cp373 = −25*r144;
    cp374 = cp373 − 25.

The only consumer of cp373 is cp374. Replace its last two rows with

    cp374 = −25*r181.

The identity is

    −25*t−25 = −25*(t+1)                            (1)

in Z[t]. It saves one addition, retaining the multiplication by −25. The value t+1 is already computed before the output row; it is not supplied freely.

The chart sources rename these registers. Their names are taken from the authenticated frozen controller maps, not inferred from positions:

| IDLE-free variant | Deleted scalar row | Changed output row | t | Already paid t+1 |
|---|---|---|---|---|
| No controller chart | cp373 | cp374 | r144 | r181 |
| Flow | chart1394 | chart1395 | chart359 | chart360 |
| Population | chart1395 | chart1396 | chart359 | chart360 |
| Both | chart1397 | chart1398 | chart362 | chart363 |

For every array the helper authenticates all three old definitions, the unique private consumer, and the earlier position of the shared packing row. It removes only the scalar row, replaces only the output instruction, and verifies that every other retained instruction is literally unchanged. There is no division, fixed-numeral change, new supplied port or zero-set assumption.

## 2. Complete all-ring identity

With each actual t as a formal cut, fresh integer-polynomial expansion gives coefficients [−25,−25] for both old and new output expressions. The whole-source proof then interprets the complete parent and child arrays. Only the locally proved affine output is normalized. Its token contains the actual t value, and the interpretation checks that the shared register is the same paid t+1 expression. Thus the proof does not assume equality merely from a reused register name.

Every retained paid register and the final output agree. For each of the four variants v,

    F_new,v = F_IDLE,v                               (2)

on identical supplied coordinates over every commutative ring. All free-port lists, positive-witness lists, eight fixed coefficient ports, illustrative fixed bindings and output ports remain exactly the same as those of the immediate IDLE-free parent. All 63 native rows, all retained outer residual positions and the complete current finalizer are checked literal.

As a separate coefficient check, the helper expands all four entire coefficient words of each parent and child in their actual paid Q. Each is compared with the effective fixed matrix coefficient dataset saved by the affine predecessor. The two X words have degree143 and 144 coefficients each; the two Y words have degree193 and 194 coefficients each. All **16 polynomials / 2,704 coefficient entries** agree exactly. Every one of the mapped 577 component rows is also checked against that frozen affine component.

## 3. Domain, degree and inherited IDLE scope

Equation(2) gives identical zero sets on the unchanged supplied interface, including positive integer zeros. No inverse coordinate map or newly chosen native witnesses are needed **between this packet and its immediate IDLE-free parents**. The same natural ordinary input x>=0 and valid fixed-program numeral recipe apply; arbitrary fixed-port values still satisfy the polynomial identities, but are not asserted to encode a simulation.

The comparison with ancestors that still contain IDLE has the weaker scope proved by the IDLE-free packet. Its forward map inserts edge_hat98=1. Its reverse language construction chooses an accepting finite history without optional identity loops and may choose new height, packed fields and native witnesses. Thus equality of ordinary-input projections is inherited. A bijection preserving all common witness coordinates with a pre-IDLE ancestor is **not** claimed.

The 99-slot controller numbering, its zero IDLE slot, fixed128-lane controller region, 340 selected-coordinate lanes and packing powers are unchanged from the IDLE-free parents. No slot is renumbered, and no duration or exponent is shortened by the affine edit.

The exact uniform degrees transfer by the entire polynomial identities (2) on identical variables, for every valid fixed-program specialization. Their surviving-leader proof is the one in the pinned IDLE-free companion, including the main-norm cancellation and extraction tie. This packet does not claim to repeat that degree proof or a leading-component computation. Its freshly computed syntactic upper bounds are recorded separately and are not mistaken for exact degrees.

## 4. Fresh complete accounting and evidence

| IDLE-free variant | M | A | Total | Positive witnesses | Outer residuals | Exact degree |
|---|---:|---:|---:|---:|---:|---:|
| No controller chart |790|827|1,617|145|20|35,587|
| Flow |789|825|1,614|144|19|53,347|
| Population |789|825|1,614|144|19|53,347|
| Both |788|823|1,611|143|18|71,107|

The counts come from the four newly emitted complete arrays, totaling **6,456 rows**, rather than from subtracting headline savings. Every paid row and every supplied port is live. Each coefficient component has **577=329M+248A** rows. Every source retains137 distinct integer literals and the same eight fixed coefficient ports. The finalizers contain62/59/59/56 literal rows, respectively. Their syntactic degree upper bounds are36,547 /54,785 /54,785 /73,023, distinct from the exact degrees in the table.

The helper builds its metadata afresh. It records new counts, source boundaries, local edits and tests, while citing the immediate parent for the inherited degree and input theorem. It does not copy old ledgers or describe predecessor evidence as newly performed.

Thirty-two supplemental signed assignments over two prime fields compare every retained register and output against the immediate IDLE-free parents. Half use the saved illustrative fixed coefficients; half vary every supplied value. These are off-zero arithmetic diagnostics. Exact local/coefficient expansion and whole-source expression proofs establish(2).

No diagnostic array, giant accepting trajectory, dense full-output polynomial or native Pell tuple is newly emitted or replayed. There is no minimality claim. Frozen predecessor files and the repository are unchanged.

## 5. Pins and replay

| Inert dependency | SHA-256 |
|---|---|
| `matrix193_idle_free_scout.py` | `33e6c22b35e6fd2c8735380f04433652686b0da20053c5446b139e8881f9ed94` |
| `matrix193_idle_free_scout.json` | `857f5af683abb1c27cba6335fd45cadbd0afc7f9c630bf312a27ea4c98aa23b7` |
| `matrix193_idle_free_scout.md` | `3502c8c69642ab3c90e5973a3668c896b34c23c0fdb88686338853573ac236d6` |
| `matrix193_affine_reuse_scout.py` | `930c44d7963a08ac96775eb328cafa1a9043d48dfa346b79c93c57f316043676` |
| `matrix193_affine_reuse_scout.json` | `c60870f886f26f21701f0a77ce02777d7d0258765dbb4f69d13e68926a6c9d4d` |
| `matrix193_affine_reuse_scout.md` | `85e15290465364db9d792c8dbcbc77914c1ef9ee78969b082154866a6dbc70ad` |
| `matrix193_entry_controller_charts.py` | `7c1e55ca1396958f234c2caf6c117702c4d69537cefcad51089498cb1e58f2bf` |
| `matrix193_entry_controller_charts.json` | `d5b4490017c9b4ad46d700d8999ad1f5dedde789dd19a3d5f7b5375a1468a571` |
| `matrix193_entry_controller_charts.md` | `27245d944d03b1d31ad79470dfd5625798834b7a47c1a03dee319f198214d122` |

After installation:

```sh
idle_affine_wip=/absolute/path/to/native-stream-queue
python3 "$idle_affine_wip/matrix193_idle_affine_reuse.py" \
  --root "$idle_affine_wip" --expect "$idle_affine_wip/matrix193_idle_affine_reuse.json"
python3 -O "$idle_affine_wip/matrix193_idle_affine_reuse.py" \
  --root "$idle_affine_wip" --expect "$idle_affine_wip/matrix193_idle_affine_reuse.json"
```

For IDLE parent files in a separate directory, add `--idle-root /absolute/idle/directory`; otherwise it defaults to `--root`. Generation uses mutually exclusive `--output`. Duplicate and nonfinite JSON are rejected, equality is recursive and type-exact, and explicit checks remain active under optimized Python.

Fresh generation and fresh normal and `-O` exact receipt replays from `/` pass.

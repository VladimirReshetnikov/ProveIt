# Positive controller charts on the entry-shared matrix source

Three complete actual-table polynomials are emitted in this packet. The flow and population charts each cost **1,619=790M+829A** with **145 positive witnesses** and exact degree **53,347**. Applying both charts costs **1,616=789M+827A**, with **144 positive witnesses** and exact degree **71,107**. Each chart preserves the full positive integer zero set of the [1,622-gate entry-shared/reduced-flow parent](matrix193_entry_flow_scout.md), after the stated elimination of controller coordinates. The ordinary input and every retained native witness are unchanged. These are improvements to the alternate matrix route; the established universal84 bound is unchanged.

The [fresh helper](matrix193_entry_controller_charts.py) emits all three complete arrays in the [receipt](matrix193_entry_controller_charts.json). It reads frozen predecessor files only as bytes and JSON. Its recursive transformer and small exact-ring routines were copied as text from the [earlier positive-controller-chart helper](matrix193_positive_controller_charts.py), then adapted to the already reduced flow source. No predecessor program is imported or executed. This packet emits no diagnostic array, performs no IDLE elimination, and materializes no new giant outer history or native Pell tuple.

## 1. Authenticated parents and source contracts

The helper authenticates these nine dependencies:

| Dependency | SHA-256 |
|---|---|
| Entry-flow Python | `0a34977902f9ada25c5007c2576d0aa2a1761bf4e8cd4d5bcad49344388a43bf` |
| Entry-flow JSON | `321a8c77b63a62d131dc52073d85f27a1f1f5086a2e19e0e42dca2df398e88da` |
| Entry-flow proof | `5a6c5330e2d29a6149965ed671bedd1838c0114deb240d1e55992960ce3d32f2` |
| Original chart Python | `b21efd94fab1ce963f39805f46721b5d69c39caf926711764d0a25a6ccbcb1a1` |
| Original chart JSON | `73eeb092a3ae9f4a9186a7b05f910024c7839c5f76c09dab535ee5b92668ae12` |
| Original chart proof | `e7fda47c1c60c168d65307edb78b77709b0b24c10827ace85d2e6b82e752f53c` |
| Composed1679 Python | `e8b2982bdf00a9be6e6e80a1b86c38f3536a5345c60adf3103e8f7356ed01317` |
| Composed1679 JSON | `a231b3ef66f0ab0f729bf50e40f87fad5a5d784e089249dbb4e93e11696a9e37` |
| Composed1679 proof | `83711eab17b18f38c2bd47ddd3d803fde5adf339f7b5bbc0be2839a3bfeff748` |

The entry-flow parent has 1,622 paid rows, 146 positive witnesses, twenty outer residuals and the complete 578-row shared coefficient component. The helper checks its literal controller definitions and finalizer. Write

    b = B−1,
    E = edge_hat0−1,
    S = edge_hat1−1,
    u = population_quotient,
    J = sum_e(edge_hat_e−1),
    P = bJ+1.

Its last two residuals are exactly

    r_flow = 1+bE−S,
    r_population = bu−(E+b−x) = x+b(u−1)−E.

The first residual is already reduced in this parent. The old four-producer expression involving J is not silently assumed to remain in the array. The helper also authenticates the literal subtraction/square pair for each of the twenty residuals, and checks the complete total-hat-sum identity for J by exact polynomial expansion.

## 2. Paid coordinate changes and all-value pullbacks

The substitutions are:

| Chart | Computed missing positive coordinate | Deleted residual |
|---|---|---|
| Flow | `edge_hat1 = 2+bE` | `r_flow` |
| Population | `edge_hat0 = 1+x+b(u−1)` | `r_population` |
| Both | both formulas, with `E=x+b(u−1)` | both |

Computed raw E or S is reused where the parent requires the corresponding raw edge word. Every operation in these formulas is emitted and counted. Eliminated residuals are set to zero only after a separate exact expansion proves that they vanish under the substitution. Their squares and now redundant finalizer additions are then removed. Constant folding uses integer arithmetic, zero/one rules and subtraction of identical values; common-expression reuse requires identical ordered operation operands. All other source dependencies are recursively retained.

Let phi_flow, phi_population and phi_both denote these polynomial coordinate maps, leaving every other supplied value fixed. For each chart the helper independently expands the missing-hat expressions from the emitted rows as polynomials in B, x, u and the remaining LOAD hat, and compares them with the displayed formulas. It then interprets the entire parent and child DAGs with an exact expression interner. The two raw-edge simplifications use the separately checked identity `hat=raw+1`; each deleted residual uses the separately proved zero identity. Every other reached parent register and the final output are checked without further algebraic assumptions. This establishes

    F_new,chart = F_1622 o phi_chart

as an all-value identity over every commutative ring. The receipt retains the complete maps, literal contracts, removed-hat expressions and retained residual wires for independent reconstruction.

The complete source is the object being counted. No coefficient evaluation, power, fixed multiplication, substituted-hat computation or finalizer operation is left outside the ledger.

## 3. Full positive integer zero equivalence

Fix any valid inherited program recipe and an ordinary input x≥0. The unchanged recipe gives B>1. All supplied witnesses, including u, are positive integers. Consequently:

* In the flow chart, the retained LOAD hat gives E≥0, hence `edge_hat1=2+bE≥2`.
* In the population chart, u≥1 gives `E=x+b(u−1)≥0`, hence `edge_hat0=E+1≥1`.
* In the combined chart, these two arguments apply in order.

Thus each polynomial map takes every positive integer child tuple to a positive integer parent tuple before any zero equation is used. The all-value identity then sends child zeros to parent zeros.

Conversely, the parent finalizer is

    N_native * (1 + sum_i r_i²) − 1.

At a positive integer zero, N_native is an integer and the second factor is a positive integer. Their product is 1, so the second factor equals 1 and all twenty residuals vanish. In particular the flow and population residuals uniquely force the missing hats to be exactly the displayed polynomial expressions. Forgetting those hats therefore gives a child zero, and reconstructing them returns the original parent zero.

The two maps are inverse bijections on the complete positive integer zero sets after the specified coordinate elimination. Equivalently, their projections onto **all common supplied ports** agree. No extraction coordinate is reinterpreted here: extraction hats and slacks, fixed coefficient ports, the ordinary input and every native supplied coordinate remain fixed. The count quotient u is retained in all three charts. This argument also covers x=0. It does not assert an analogous positive-real theorem: u>0 need not imply u≥1, and the finalizer argument uses integrality.

The unchanged parent simulation theorem therefore supplies the same program-specific ordinary-input language. The fixed matrix table and instruction grammar remain independent of the program; a valid fixed-program recipe supplies the unchanged eight fixed coefficient ports. Arbitrary assignments to those ports still satisfy the polynomial identities, but are not asserted to encode a valid simulation.

## 4. Complete equality to the original charts and exact degree

Degree is transferred through a freshly checked complete polynomial identity, rather than estimated from the new source's syntactic degrees.

First the helper establishes

    F_1622 = F_1679

on identical supplied coordinates. It independently expands all four coefficient polynomials in the common paid Q. The two X words have degree 143 and 144 nonzero coefficients each; the two Y words have degree 193 and 194 nonzero coefficients each. The complete integer coefficient lists agree between the entry-shared outputs cp312, cp313, cp580, cp581 and the older outputs mix323, mix324, mix631, mix632. The paid Q expressions themselves are checked equal before these univariate identities are used as common cuts.

The remaining nonliteral change is the flow identity

    (J−E−S)+((B−1)J+1)−B(J−E) = 1+(B−1)E−S,

which is checked by exact multivariate expansion. With only these proved coefficient and flow cuts, expression interning compares all 1,042 common paid parent registers, all six native inputs, all 63 native rows, all twenty residuals and the complete output.

Next the helper reconstructs each actual-table array of the pinned [original controller-chart packet](matrix193_positive_controller_charts.md), directly from the pinned composed1679 JSON. It checks the full array, supplied interface, output, register map and removed residuals against that frozen receipt, and freshly rechecks each full pullback. The formal missing-hat polynomials of the new and original charts are exactly equal. Hence, on the same remaining variables,

    F_new,chart
      = F_1622 o phi_chart
      = F_1679 o phi_chart
      = F_original,chart.

The exact degrees from that pinned proof therefore transfer unchanged for every valid fixed-program specialization: 53,347 for either single chart and 71,107 for both. For orientation, that proof has degree s=3 for Q in a single chart and s=4 in both; N=340+128+4=472 and the longest coefficient block has length194. Its full degree formula is

    (36N+4*194−8)*s+67 = 17,760s+67.

It includes the main-norm cancellation and the bounded-high extraction tie. The present proof does not substitute a nonlinear chart into an old leading monomial and assume that no cancellation occurs. It transfers the entire polynomial to the already proved chart on identical variables. No new dense degree computation or giant specialization is claimed.

## 5. Complete ledgers and evidence

The counts below are recomputed from the three complete emitted arrays, not obtained by subtracting a proposed saving:

| Actual chart | M | A | Total | Positive witnesses | Outer residuals | Exact degree |
|---|---:|---:|---:|---:|---:|---:|
| Flow |790|829|1,619|145|19|53,347|
| Population |790|829|1,619|145|19|53,347|
| Both |789|827|1,616|144|18|71,107|

Each array has unique producer names, valid topological order, and output liveness for every paid row and every supplied port. All 578 parent coefficient rows remain represented in its register map and are checked by the full pullback. Each source uses 137 distinct integer literals; the same eight fixed coefficient ports are separately supplied by the recipe. The source retains the IDLE edge and its witness.

Fresh supplemental checks compare every mapped parent register and the full output for 24 signed assignments over two prime fields, eight per chart. Half use the saved illustrative fixed coefficients and half vary all supplied values, including fixed ports. These are off-zero algebraic tests, not compiler histories. The exact cut identities and full pullback checks provide the proof.

Only the three actual-table sources are emitted here. The small diagnostic arrays remain in the pinned original chart packet and are neither emitted nor replayed in this successor. No reduction is claimed for a diagnostic lacking the actual entry-sharing structure. No new native Pell tuple or giant outer trajectory is materialized.

The final standalone helper and receipt pins are:

* Python: `7c1e55ca1396958f234c2caf6c117702c4d69537cefcad51089498cb1e58f2bf`.
* JSON: `d5b4490017c9b4ad46d700d8999ad1f5dedde789dd19a3d5f7b5375a1468a571`.

Fresh generation and fresh normal and optimized exact receipt replays from `/`, using `/tmp` as the explicit dependency root, passed. After installation:

```sh
entry_chart_wip=/absolute/path/to/native-stream-queue
python3 "$entry_chart_wip/matrix193_entry_controller_charts.py" \
  --root "$entry_chart_wip" --expect "$entry_chart_wip/matrix193_entry_controller_charts.json"
python3 -O "$entry_chart_wip/matrix193_entry_controller_charts.py" \
  --root "$entry_chart_wip" --expect "$entry_chart_wip/matrix193_entry_controller_charts.json"
```

Use `--write FILE` to regenerate. The parser rejects duplicate keys and nonfinite JSON; recursive type-sensitive receipt equality and explicit exception checks remain active under `-O`. This packet changes no frozen predecessor bytes or repository files.

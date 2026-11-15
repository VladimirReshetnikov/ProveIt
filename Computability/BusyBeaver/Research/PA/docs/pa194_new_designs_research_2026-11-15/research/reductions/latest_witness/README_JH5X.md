# PA194JH5X: a coupled positive-join and independent-consequent emitter

PA194JH5X is a second accepted construction with 194 working states and one separate terminal state. The dense table is `machines/PA194JH5X/machine.tm`, with start 0, working states 0 through 193, and terminal 194. It starts on the all-zero two-way infinite binary tape. Every transition writes and moves, including the transition into the terminal state.

Let `X = U(D, U(D,H) -> 1)`. In addition to replacing the equality-witness head by

    U(D, E(H,D) -> 1) -> A,

the source replaces the old first head `(X -> 1) -> H` with the positive join

    (X -> H) -> H.

The consequence `A` in the equality-witness head is independent of `D` and `H`. That independence recovers the original witness schema at `A=1` and supplies explosion without the old first head. Once explosion has been obtained, the old first head and the positive join have fixed primitive-recursive proof translations using K, S, Peirce, and modus ponens. This dependence is essential: the first-head change is not justified in isolation. The parent report supplies the checked proof lists and the written iPRA calibration.

The remaining quantifier-distribution head has its ordinary, unexchanged premise order. All six selected schema parameter maps are the identity. The implementation retains explicit-binder generalization `U(c,h)`, no-dummy-push MP, cache-only Shift, and eleven AX entries with the real fourth field.

## Exact construction and validation

| Item | Result |
|---|---:|
| Fixed controls | 134 |
| Raw reader controls | 69 |
| Simultaneous folds | 9 |
| Working states | 194 |
| AX macro tokens | 188 |
| Primitive source sites | 3,683 |
| Complete branch outcomes | 4,794 |
| Construction-runtime symbolic steps | 1,502,607 |
| Independent literal symbolic steps | 1,097,281 |
| Largest literal symbolic case | 388 |
| Whole blank startup transitions | 57,922 |
| Maximum source-path depth | 34 |
| Nonhalting source-boundary closures | 4,793 |

The independent literal checker reconstructs four list-sweep lemmas directly from the rows and checks every source instruction and both decrement outcomes over nine arbitrary natural primary registers, an arbitrary nonempty finite spare list, an arbitrary nonnegative affine gap, and complete blank exteriors. It imports neither the builder nor the arithmetic-box checker. Every recorded affine duration has nonnegative integer coefficients and constant at least 3. All nonhalting boundaries have zero net head motion, zero header overflow, and exactly the independently resolved successor source address. The single halting outcome has duration exactly 3.

The complete blank startup check compares the entire finite support of the tape. It is not a fixed-window comparison. Every working control is reachable in the transition graph. The native and dense tables are related by the supplied label bijection. The independent census finds the table absent from the current 139 spanning classes and distinct from PA194H5X under arbitrary start-preserving state renaming, reflection, global bit exchange, and erasure of halting-transition write/move actions.

Dense SHA-256:

    70be32fe352ee0fb29581f1037948f429334cfc9c6bcaa813aba43c4efba0148

Native SHA-256:

    957fef85080849e88bba4e82732065a350d382d489a032ddbc03756e8ef0c5e1

Independent contracts SHA-256:

    f70a4c7f923701082bd2a943ba12da97738c21e4b29edf73b06d1e76d8131a35

## Offline reconstruction

The accepted grammar and all nine folds are frozen; the deterministic builder performs no search. Python 3.10 or newer and its standard library suffice. The shared `construction/vendor`, `construction/inputs/raw.native.tm`, `construction/inputs/nodes.json`, `verification/reference`, and `check_emitter.py` files are supplied by the PA194H5X component, byte-for-byte unchanged. Run without `-O` or `PYTHONOPTIMIZE`.

```sh
python3 -B construction/build_PA194JH5X.py --output /tmp/rebuilt-PA194JH5X
python3 -B check_emitter.py /tmp/rebuilt-PA194JH5X --output /tmp/rebuilt-JH5X-emitter.json
python3 -B verification/check_literal_JH5X.py /tmp/rebuilt-PA194JH5X --output /tmp/JH5X-literal-replay
```

Copy the four independent certificate files from `/tmp/JH5X-literal-replay/PA194JH5X/` into `/tmp/rebuilt-PA194JH5X/independent/`, then run:

```sh
python3 -B verification/physical_ipra_audit_JH5X.py --machine /tmp/rebuilt-PA194JH5X --output /tmp/JH5X-closure-audit.json
```

The frozen full results are retained under `machines/PA194JH5X/independent/` and `machines/PA194JH5X/physical_ipra_audit.json`. The builder's successful full replay is `construction_receipt.json`; the exploratory assembler's original receipt is retained separately as `receipt.json`.

## Status and provenance

The source change is material: the first and fifth logical heads change together, with a proof dependency between them. Its 188-token word is shorter than the 189-token PA194H5X word, but both accepted physical tables have 194 working states. No machine below 194 states is claimed. The attempted 187-token JA extension and the continuing grammar/physical searches are research, not a lower-bound argument.

This component uses the same unchanged compiler, register runtime, literal induction engine, and source resolver recorded in `PROVENANCE.json`. The shared licenses and attribution remain applicable. Its executable symbolic checks and fixed proof lists are mathematical evidence; no completed end-to-end Lean or Rocq verification is claimed.

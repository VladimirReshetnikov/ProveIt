# Further K215 proof simplification

Pinned source: VladimirReshetnikov/ProveIt at
`cbf94cb552a3b49509e0eee80e7455d4eb5974c6`.

Start with `report.pdf` or its editable `report.tex`.

## Recommendations and status

1. Decoder prefix: delete its second source language. The exact map identifies
   202 alternate nodes with 179 program forks plus23 primitive leaves, retaining
   every 234 physical role and 281 block. This simplifies the separately checked
   prefix component. It does **not** yet reduce the production endpoint closure.
   Universal direct-walk soundness, physical block composition and residual
   primitive/return semantics remain required.
2. AX words: infer each 156-atom word from its actual DAG, but retain the old
   checker and soundness theorem. The small draft saves 787 bytes across two
   modules including its helper, while adding six lines; for K215 alone it saves
   only 27 bytes and adds a module. It is a maintenance experiment, not a large
   endpoint reduction or a measured speedup.
3. Rocq: reuse the existing generic loop proof for `z465`, preserving its public
   statement. The declaration changes from 9 to 5 lines and 475 to 171 bytes. The
   producer template and all affected generated outputs must stay synchronized.
4. Optional experiment: a shared guarded-subtype interpretation is mathematically
   coherent, but its 108-line kernel and 71-line comparison client exceed the
   current 89-line target (99 with environment helpers). It is not recommended
   for current source-size reduction. Named constructibility syntax is excluded.

All new `.lean` and `.v` files are **uncompiled proposals**. There is no new
end-to-end kernel check, timing claim, internal PA/ZFC derivation, machine-state
reduction or change of the target machine. Historical compilation claims in
pinned upstream documents remain their own evidence, not checks rerun here.

## Contents

- `root/`: exact AX source snapshots, inference audit, helper/overlays and patches.
- `decoder/`: full node/role map, direct-program checker pilot, source snapshots,
  mathematical obligations and finite source-data audit.
- `rocq/`: proposed producer patch, typed comparison client, status review,
  exact pinned sources and audit.
- `lean/`: optional guarded-subtype experiment, source snapshots in JSON,
  explicit costs and finite capture/equality regressions.
- `review/`: independent data checker and mathematical validation note.
- `evidence/`: current verification README, proposal index and recent commits.

The decoder pilot imports the old block provider as a migration convenience.
That provider must be split before the obsolete source-language dependency can
actually disappear. The pilot's terminal checker binds a physical action to a
non-internal source edge, but does not prove that action implements the opcode.
The 6,176 outcomes are counted/mapped, not newly executed or kernel verified.

For the AX draft, copy `root/drafts/MacroWordInference.lean` into the repository's
`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/` folder and inspect the two proposed
module patches. Also update `generate_l2axiomsdom.py`; no complete producer patch
is claimed. Re-elaborate the unchanged checker and evaluation proofs, then the
relevant endpoint clients, before accepting this change.

The Rocq diff targets the shared `NEW_EQ` template in `regenerate218.py`, from
which the 215 and 217 producers derive their libraries. It is not a claim that
editing only a generated215 file is sufficient.

## Reproduce finite checks

Python 3.12 was used; only its standard library is required. From the extracted
package root:

```sh
python verify.py
```

The driver first verifies all sealed files, then runs only the seven newly
written audit/generator programs in a temporary copy. It checks the recreated
receipts, mappings, overlays and proposed diffs byte for byte. No upstream
Python, Lean or Rocq code is executed. Do not use `python -O`, because component
diagnostics use assertions; the driver rejects optimized execution.

`VERIFICATION.json` records the packaged run. For a new receipt, use:

```sh
python verify.py --out /path/to/new-receipt.json
```

Choose an output outside this package to keep its sealed files unchanged.
Finite data checks and mutation controls are not proofs of the quantified
semantic theorems. See the report's acceptance gates before production adoption.

To rebuild the PDF in a normal pdfLaTeX installation:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

Inherited repository notices are retained in the source files and
`LICENSE.ProveIt`. No remote branch or repository file was modified by this review.

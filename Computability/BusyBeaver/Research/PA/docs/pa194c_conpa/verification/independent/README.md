# Independent physical verification of PA194C

From the package root run:

```sh
python3 -B verification/independent/check194C.py
```

Python 3.10+ and the standard library suffice. Do not use optimization (`-O`)
or disable assertions. The checker imports no construction compiler or
arithmetic-box oracle. It reads the literal dense and native tables under
`construction/rebuilt_194C/` and checks their explicit label bijection.

Two independent source-edge resolvers must agree and reproduce the exact
published 195C instruction file in `reference_inputs/195C.instructions.json`.
The checker derives four generic unary-list lemmas from the physical rows,
then checks all 4,749 instruction outcomes over arbitrary natural register
values, both decrement branches, arbitrary nonempty finite spare lists, and
the affine header-distance parameter. The output records every contract's
positive duration and head displacement. An independent byte-array simulator
compares the full 57,922-step blank tape with its expected source frame.

Results are written to `recorded_C/PA194C/`: `receipt.json`, `contracts.json`,
`list_lemmas.json`, and `blank_seed.json`. The receipt includes the literal
hashes, 3,649 source sites, 1,096,302 symbolic operations, maximum 403 per
outcome, and minimum duration constant 3.

The checker compares the new graph with the two supplied positive 194-state
graphs and their reflections. The separate script
`comparison/check_all194_novelty.py` covers all seven old literal forms in the
full census, including the later eight-fold allocation and the rejected scanner graph.

The generic symbolic engines in `reference/` are inherited and credited by
their README and licenses. Independence here means independent source-edge
resolution and literal physical checking relative to the construction
compiler, not a claim that all shared mathematical infrastructure was
independently invented. Logical consistency calibration is in the report
and its source references; this executable is not an end-to-end PA proof
compiler or a new Lean/Rocq theorem.

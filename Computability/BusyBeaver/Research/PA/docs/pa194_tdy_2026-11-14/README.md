# PA194TDY — 194-state physical register-cycle design

This package supplies an explicit deterministic binary, single-tape Turing
machine whose nonhalting is equivalent to Con(PA) by an ordinary PA proof
transported from the primary PA194 source calibration.

**No machine with fewer than 194 working states was established.** PA194TDY is
the 194-state fallback. It changes the physical locations of registers T, D,
and Y; it preserves the logical calculus and complete source program.

Read `report/report.pdf`; its complete LaTeX source is `report/report.tex`.

## Literal machine

- Dense table: `artifacts/pa194_tdy.tm`.
- Alphabet: 0 and 1; blank symbol 0; two-way infinite tape.
- Start: state 0, head at position 0, entirely blank tape.
- Working states: 0 through 193. Halt label: 194, excluded from the count.
- Each row is `state read write L_or_R next`.
- Native table and both numbering maps are included in `artifacts/`.

Dense SHA-256:

```text
84bfe1368312c7c71c9e4706de7cb65923310e25f8d472997c9c57c5aedd7934
```

Native SHA-256:

```text
2f6e2342151be7c9f7fb8025f81063525c5d276605d2fa87535a9c7d1498755d
```

## Verification

Run from this extracted directory, with Python 3.10+ and Node.js 18+:

```bash
python3 verify.py
node verification/verify_tdy.cjs
python3 -B verification/literal/check_tdy.py
python3 comparison/verify_novelty.py
node research/runtime193_permutations.cjs
```

The first two commands check the four-row reconstruction, dense numbering,
source instruction graph, all 4,780 arbitrary-register symbolic outcomes,
unchanged arithmetic boxes, and exact 57,594-step whole-tape startup.
The third derives four unary-list sweep lemmas from the literal rows, checks
all 4,780 outcomes without arithmetic-box oracles, and records positive affine
physical durations (nonnegative coefficients, constant at least three).
It separately repeats the exact startup with a bytearray tape.
The comparison command checks the candidate against the supplied corpus
evidence at the pinned snapshot. The last command replays the uniform
obstruction to the examined 193-state fold and explicitly checks the 40,320
allocations fixing the initial nonzero register's physical position.

The first two universal source checks use inherited arithmetic-box lemmas;
the third derives the required tape-sweep facts directly from candidate rows.
None infers universal behavior from a bounded collection of numerical cases.
The repository's stronger end-to-end Lean/iPRA formalization remains open;
this package does not claim to complete it. The included generic Lean runtime
file takes `BoxLemmas` as hypotheses and is an inspection dependency, not a
standalone proof-assistant build.

## Comparison scope

The repository snapshot is:

```text
4be5c6e3a10292a7466f5d3687e3b39615ff049b
```

The complete packet ledger and scoped literal-table census cover all 61 filed
deliveries and all 11 ZIP files in `docs/incoming` at that snapshot. The scope
includes 535 retained filed representative tables and the direct PA tables;
`comparison/README.txt` states the JSON-source and code-only exclusions.
It distinguishes literal-table identity, differences in
starting control, reported mathematical claims, auxiliary constructions, and
rejected candidates. Files containing a 193-state table are not automatically
193-state consistency machines. See `comparison/` for the complete ledger,
table data, and precise counts.

PA194TDY is an extension of the earlier physical-register allocation method.
It is not claimed to be a new logical consistency encoding. All four changed
rows are used in its blank startup, and its source-frame representation differs
throughout execution. Exact novelty checks include all spanning roots,
state renaming, reflection, global bit exchange, and ignored terminal actions.

## Report build

```bash
cd report
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The report was compiled and rendered for visual inspection. The retained
reference `.tex` files are original fragments, not separate standalone papers.

## Research artifacts

`research/runtime193_rejected.native.tm` is deliberately a **rejected**
blank-start candidate. It reaches a provable infinite writing ray. The
uniform certificate explains why all 9! register layouts of that particular
fold fail from its fixed blank start. This is not a general lower bound of 194.

Optional bounded local-contraction searches and their limits are documented
in `research/REPRODUCE.txt`. They are not needed to verify PA194TDY.

## Attribution

The source program, numerical calculus, compiler ancestry and arithmetic
engine are inherited from the cited ProveIt packets and James Chang's PA196
development, with earlier K-family runtime ancestry. Original notices,
licenses and source paths are retained under `reference/`. This package adds
the T/D/Y allocation, its literal implementation and replay checks, the
combined snapshot comparison, and the stated bootstrap obstruction.

`SHA256SUMS` covers the complete delivered package except itself.

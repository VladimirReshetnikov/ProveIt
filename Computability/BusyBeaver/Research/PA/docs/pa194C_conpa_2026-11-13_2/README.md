# PA194C: a materially different 194-state Con(PA) machine

The strict target of fewer than 194 states was not attained. The completed
fallback is **PA194C**, a fully specified binary, one-tape, blank-start Turing
machine with 194 working states and a separate halt label. The report gives an
ordinary mathematical proof of

\[
\mathrm{PA}\vdash
\bigl(\neg\operatorname{Halt}(\mathrm{PA194C},\mathrm{blank})
\leftrightarrow\operatorname{Con}(\mathrm{PA})\bigr).
\]

Read **`report/pa194C_conpa.pdf`** for the full comparison, calculus, proof,
complete transition table, exact verification scope, and all 36 archive entries.
The complete LaTeX source and included fragments are in the same directory.

## Literal machine

The authoritative table is **`construction/output/pa194C.tm`**.

- Working states: 0 through 193. Initial state: 0. Halt label: 194.
- One two-way infinite tape; alphabet `{0,1}`; initially all zero.
- Initial head coordinate: 0. Every transition moves exactly one cell L or R.
- Exactly 388 rows: `state read_bit write_bit direction next_state`.
- All 194 working states are reachable in the transition graph. This does not
  assert that they all occur in the actual blank execution.
- SHA-256: `d759313c03b515293fe06b12769fa1771d3829a2bad89febaa9b4391990f3a4b`.

## Why this is a material alternative

The previous 194-state candidates retain the original proof-command controller.
PA194C combines the primary PA194 decoder (67 raw readers, seven contextual
folds) with the previously established Combined controller. The count is
`134 + 67 - 7 = 194`.

Original Shift halts when `t+h=1`; the new Shift halts exactly when `h=1`.
Original successful MP leaves its consequent in T, retains D, and pushes zero;
the new MP leaves the consequent in H, clears T and D, and leaves the stack
unchanged. These are different command semantics. Six native transition rows
change, and the source shrinks from 3,673 to 3,649 primitive instruction sites.
The Combined controller itself is credited prior work; its verified composition
at 194 states is the new construction.

The new transition graph differs from every existing 194-state table in the
pinned corpus, even under arbitrary state renaming, arbitrary root choice,
tape reflection, and simultaneous read/write symbol complementation. The latter
is only a stronger cosmetic-novelty check, not a blank-zero semantic equivalence.

## Complete verification

Python 3.10 or later and the standard library suffice. From any directory:

```sh
python3 -B /path/to/pa194C_conpa/verify.py
```

Or run the components from the package root:

```sh
python3 -B construction/build194c.py
python3 -B construction/verify194c_independent.py
python3 -B construction/command_audit/check_composite_commands.py
python3 -B comparison/compare_candidate.py --candidate construction/output/pa194C.tm
```

Assertions must be enabled: do not use `-O` or `PYTHONOPTIMIZE`.
No network, compiler, solver, or proof assistant is required for these commands.
The optional heuristic searches are not part of reconstructing the result.

The delivered receipts record:

| Quantity | Result |
|---|---:|
| Complete resolved source sites | 3,649 |
| Universal primitive branch contracts, each implementation | 4,749 |
| Builder symbolic proof transitions | 1,507,397 |
| Independent literal-tape symbolic proof transitions | 1,096,302 |
| Generic list lemmas rederived from actual rows | 4 |
| Positive-duration constant lower bound | 3 |
| Jointly checked local fold cases | 28 |
| Symbolic command-algebra cases | 188 |
| Exact blank initialization | 57,922 tape transitions |

The symbolic contracts quantify over arbitrary natural register values, an
affine gap, and an arbitrary nonempty finite spare list. They are not bounded
register tests. The independent checker uses no arithmetic-register oracle.
It independently resolves source jumps, rederives the four list lemmas, and
compares the entire blank-start tape support. Initialization is 232 tape
steps shorter than primary PA194; no uniform runtime improvement is claimed.

The mathematical proof additionally supplies logical refutation translations,
the ten-entry command compiler, a refutation word that halts from every incoming
store, and PA formalizability of positive finite simulations. It uses no PA
reflection principle. This release does **not** claim a freshly compiled
end-to-end Lean or Rocq theorem or a completed iPRA endpoint.

## Corpus and provenance

All comparisons use ProveIt commit
`768c2be1a8e4d2fcf8aa3443c7b0f084d145734c`.
The read-only census covers all 36 incoming archives, 49 distinct recursively encountered ZIP
payloads, 77 archive references, and direct PA tables. Its stated numeric table
recognizer finds 2,519 occurrences, 606 byte identities, and 437 action-graph
classes. These include rejected experiments and controls, not just supported
consistency machines. The complete scope and limitations are in the report.

The prior 194-state corpus consists of three supported mathematical designs
(two decoder allocations and one A/D register layout) plus an explicitly
rejected scanner experiment. The seven prior byte forms are included under
`comparison/reference194/`. The entire large ancestor archive collection is
not repeated; its exact identities and member paths are retained.

The full corpus census can be rerun with the pinned repository:

```sh
python3 -B comparison/census_current.py --repo /path/to/ProveIt --output /tmp/pa-census
```

Attribution, source hashes, original license notices, and the exact inherited
component boundary are preserved in `construction/PROVENANCE.json`,
`construction/construction/licenses/`, and the copied source headers. The
construction inherits the PA196 register engine and source framework, the
PA195 diagonal calibration, the separate-head emitter, the Combined commands,
and the primary PA194 reader allocation. It does not claim those earlier
ideas as new.

## Package map

| Path | Contents |
|---|---|
| `report/` | Compiled article, LaTeX source, full transition table, archive ledger |
| `construction/output/` | Authoritative table, native table, source map, source sites, labels, receipts |
| `construction/independent/` | All universal contract summaries, rederived list lemmas, complete blank seed |
| `construction/command_audit/` | Ten-entry command checker and symbolic audit |
| `construction/proof_sources/` | Detailed inherited logical calibration and command proof fragments |
| `construction/construction/` | Pinned parent194 compiler, grammar, folds, register engine, and licenses |
| `comparison/` | Full census, all archive and direct-table catalogues, graph comparison, novelty receipt |
| `search/` | Optional bounded search programs, exact inputs, logs, and honest negative-result scope |
| `validation/` | Fresh portable full-suite replay logs and receipt |
| `verify.py` | One-command complete verification driver |

Rebuild the article from `report/` with two normal `pdflatex` passes on
`pa194C_conpa.tex`, or use `latexmk -pdf`. Verify release hashes with
`sha256sum -c SHA256SUMS` from the package root before regenerating evidence.
Replaying checks can rewrite receipts, including timings.

No global optimality claim is made, and unsuccessful bounded searches are not
proofs that 193 states are impossible. The report is dated 13 November 2026 in
Pacific time; some supplied archive names use 14 November in UTC.

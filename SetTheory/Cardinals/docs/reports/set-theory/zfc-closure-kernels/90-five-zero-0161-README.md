# Theory and formula-codec controls

This contribution contains a mathematical obstruction, a finite propositional
countermodel, and reproducible codec/compiler cost experiments. It does not
claim a consistency machine below 245 states.

## Findings

1. Removing only `x ⊆ V` from the power-container axiom produces the exact
   theory `CP− + GIC + IR` described in `theory_codec_note.tex`. ZFC proves this
   theory consistent. The proof uses pseudo-hereditarily small sets at
   `κ = beth_ω`, following Greg Oman's model construction, with a self-contained
   sethood/rank argument, a direct check of the weakened CP, and a uniform
   satisfaction-based check of the full GIC schema. It also shows explicitly
   that this model fails the original CP at `p = ω`.
2. The three-valued Łukasiewicz implication matrix validates the source's
   implicational axiom with fourth input fixed to truth, even with K, ex falso,
   and double-negation elimination, but refutes S. This prevents that shortcut
   from being a complete propositional calculus under substitution and modus
   ponens. It does not itself analyze the entire first-order collection theory.
3. Four-constructor unequal-prefix coding and a three-tag encoding retaining
   equality via atom-argument parity pass the arithmetic and literal register
   contracts, but cost more under the measured direct backend:

| Encoding | Register DAG nodes | Instruction leaves | Wade working states |
|---|---:|---:|---:|
| Uniform four, exact source control | 219 | 6460 | 281 |
| Uniform four, All/Eq tag swap | 219 | 6477 | 281 |
| Prefix multipliers 2/4/8/8 | 231 | 6519 | 294 |
| Prefix multipliers 2/8/4/8 | 231 | 6471 | 294 |
| Relation/equality argument parity | 227 | 6512 | 289 |

The 281-state control uses the original 219-node source, not the 128-rule routed
grammar behind the 245-state candidate. These counts must not be subtracted
directly from 245. Every emitted Wade table has the inherited missing edge
`(1.inc, 1)` and terminal target `halt`; they are raw compiler controls, not
completed, calibrated blank-start consistency machines.

4. Two further CP rearrangements are exactly equivalent to the original axiom:
   absorb transitivity into the subset consequence, or merge the separate
   universal quantifiers. The latter reduces literal instructions but requires
   a fourth variable name in its direct spelling. Reserving variable zero and
   shifting the CP-only labels gives 243 DAG nodes, 6,386 instruction leaves,
   and 306 raw Wade states. A closed fixed-label fused CP gives 244 DAG nodes,
   6,344 leaves, and 306 states. These are all larger than the 281-state exact
   control. The complete table, ordinary equivalence proofs, and the variable
   capture accounting are in the note. `cp-fusion-results/summary.json` also
   includes 4,674 exhaustive finite local-formula equivalence checks, exact AX
   stack/specification checks, and literal new-macro contracts. Both the finite
   checks and raw compiler counts have their limitations stated explicitly.

## Reproduce

Python 3.10 or later, standard library only:

```sh
python codec_source_experiment.py
python check_codec_experiments.py --backend backend
python check_truth_restriction.py
python cp_fusion_experiment.py --backend backend
python verify.py --output /tmp/theory-reproduction
```

Each codec receives 2,304 constructor round trips, 19,999 positive-code inverse
and strict-argument checks, and 1,296 literal register macro contracts. The
uniform-four control is also checked for exact rooted source-tree equality
against the input. Results are in `codec-source-results/checks.json` and
`codec-source-results/truth-restriction-matrix.json`.

`verify.py --output PATH` is the recommended reproduction entry point. It
requires a separate destination, regenerates every default finite codec,
matrix, and CP control, compares frozen JSON and raw table bytes exactly, and
checks that frozen inputs and results have not changed. The output directory
receives `verification.json` plus each command's stdout/stderr. Run with
assertions enabled, without Python's `-O` option.

The source generator takes `--source PATH` and `--output-dir DIR`. The checker
accepts the same options. Its `--backend` option is optional: omitting it runs
the codec/register checks without emitting the raw binary tables.

To compile the note, run `pdflatex theory_codec_note.tex` twice. The document's
mathematical proof is written in ordinary ZFC; it has no Lean/Coq endpoint.

## Provenance and licensing

- `inputs/original219.json` is copied byte-for-byte from the ProveIt incoming
  archive `zfc-axiom-symmetry-20261018`, path
  `research/axiom_search/data/original219.json`. It represents the original
  source219 DAG, with the same literal proof-search kernel as the upstream
  source.
- `backend/TMBuilder.py`, `backend/tm.py`, and `backend/tmdb.py` are copied
  byte-for-byte from the ProveIt incoming archive
  `sub246-audit-and-alternatives`, path
  `research_sub246/logical_routes/permuted_rows/backend`. They carry Andrew
  James Wade's MIT No Attribution license in `notices/LICENSE.Wade`.
- `notices/LICENSE.ProveIt` is retained for the copied ProveIt input.
- `provenance.json` records SHA-256 hashes and exact archive-relative origins
  for these copied files.
- The new scripts and note were created for this research contribution. The
  finite checks are computations on the copied source, not replacements for
  the upstream proof-search calibration or a new binary simulation proof.

Primary references:

- Greg Oman, *On the axiom of union*, Archive for Mathematical Logic 49
  (2010), 283–289, DOI
  [10.1007/s00153-009-0163-1](https://doi.org/10.1007/s00153-009-0163-1).
  [Author PDF](https://faculty.uccs.edu/goman/wp-content/uploads/sites/15/2021/02/On_the_axiom_of_union.pdf).
- [Upstream source254](https://github.com/jeff87654/busy-beaver/tree/zf-254/ZF/m254).
- [ProveIt candidate-routing245](https://github.com/VladimirReshetnikov/ProveIt/blob/main/Computability/BusyBeaver/Research/ZFC/candidate-routing245/README.md).
- [ProveIt incoming research archives](https://github.com/VladimirReshetnikov/ProveIt/tree/main/docs/incoming).

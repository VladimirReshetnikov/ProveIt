# A 239-state binary Turing machine for ZFC consistency

**Result:** the supplied one-tape, two-symbol machine has **239 working states** and starts on an entirely blank zero tape. The report gives an ordinary mathematical proof, formalizable in ZFC, of

\[
\mathrm{ZFC}\vdash\bigl(\neg\operatorname{Halt}(M_{239})\leftrightarrow\operatorname{Con}(\mathrm{ZFC})\bigr).
\]

The exact construction, complete unbounded runtime check, blank initialization, local reduction, and independent local replay have passed. **A newly compiled Lean/Rocq theorem for the exact 239-state table is not included.** The logical source calibration is inherited from the pinned ProveIt construction; the open internal PA endpoint remains separate.

## Read first

- `report.pdf`: the 17-page research report, including the full canonical transition table.
- `report.tex` and `sections/`: its editable LaTeX source.
- `machines/zfc239.tm`: the final table in canonical numbering.
- `machines/zfc239_old.tm`: the identical machine with inherited labels for reviewing the three edits.
- `machines/renumbering.json`: the exact bijection between labelings.
- `verification/reproduce.py`: the main reproduction entry point.

This packet was prepared on 19 October 2026 against ProveIt commit `13ec39ed43148b1807f51ed6e6528e1c84659562`. No remote repository write, commit, or pull request was performed.

## The saving

Starting from `candidate-rotation240/zfc_rotation240_old.tm`, make precisely these changes:

| Inherited row | Old | New |
|---|---|---|
| `147/0` | `0 R 169` | `0 R 80` |
| `80/0` | `0 R 25` | `0 L 106` |
| `91/1` | `0 L 50` | `1 L 167` |

Delete both rows of state 169. The only incoming edge to 169 was `147/0`. Every other row is preserved.

The decisive change is the delayed erasure at `91/1`. Keeping the 1 temporarily lets existing states 167 and 151 distinguish the original caller from the context of deleted state 169. Existing control paths then produce exactly the old tape and head position. The successful search allowed a helper row to change along with the state fold.

The six exceptional comparisons take old/new durations `1/5`, `1/1`, `1/3`, `1/5`, `1/1`, and `3/11`. All unspecified exterior cells are independent symbolic variables. The required additional guard, `q=169 and tape[h]=1 => tape[h+1]=1`, was proved over the exact old initialization and every unbounded instruction case. At the 32 symbolic runtime entries, the right-hand 1-run has length `G+K`, where `G >= 0` and `21 <= K <= 59`.

The direct proof of the final 239-state table supplies another route: it checks the original complete source instruction family without using the interval restrictions that guided discovery.

## Exact model and hashes

The canonical working states are `0..238`; state `239` is the separate halt state and has no outgoing rows. Start is `0`, dispatcher is `84`, tape alphabet is `{0,1}`, and there are 478 transition rows. The tape is infinite in both directions. A line `q b w D r` writes `w`, moves one cell in direction `D`, and enters state `r` when state `q` reads `b`. The comment `#! start 0` declares the start state. All cells initially contain zero and the head starts at coordinate zero.

| File | SHA-256 |
|---|---|
| `machines/zfc239.tm` | `4447a2423907f2b96e8bcd6c88ed2d1e353f925fb8cf36ca913224ddce5914ba` |
| `machines/zfc239_old.tm` | `76a9574ac0385b96dbd558fa852a222e1d9025e48e34dc3590384146726d2a9b` |
| `machines/sites_logical.json` | `74b1e7f73cc3ffe7761e36ab2d57a26e0ba34d3ac624f2472799e6ac41d5a51d` |
| `reference/zfc240_old.tm` | `547dd69da66f66dd48238a53d34b52a3ce85bb6c7d01534dd1cfb815507f248f` |

## What was verified

The fresh full runtime check returned `UNIVERSAL_MATHEMATICAL_PASS` for all **8,386 guarded cases** of the unchanged **6,455-leaf** source, using **2,330,575 symbolic rules**. The cases range over every natural primary register value, arbitrary additional header gap, arbitrary first spare value, and an arbitrary finite remaining spare list. Four exact one-block lemmas support structural induction over that list. Literal steps and homogeneous-run induction are the other execution rules. The minimum certified actual duration is 13 steps.

This is not a bounded execution experiment. The finite limit of 4,000 in the checker bounds proof construction within one case, not actual machine time or register values. The mathematical soundness of the rules is explained in the report; the Python program is not a proof-assistant kernel.

The complete initialized tape is reached after **409,835** transitions, at inherited state 96 / canonical state 84 and head `-5`. The marker is at `-6`, header at `176`, and all 351 one-cells are recorded explicitly. The nine logical values are `(3,0,0,0,3,0,0,0,0)` and there are 167 spare blocks of value 1. All other cells are zero. Independent sparse and dense implementations agree.

The old initialization takes 409,691 steps. Its exceptional visit counts `(18,12,6,3)` give the exact additional time

\[
4\cdot18+2\cdot12+4\cdot6+8\cdot3=144.
\]

The source identity check reconstructs all 203 DAG rows and all ordered leaves from the pinned Lean source definitions as literal data. It also checks zero-padding normalization at every source join, including the empty initial program counter. The spare blocks are auxiliary storage: all source register operands are in `0..8`.

## Reproduce

From this directory, using Python 3 with assertions enabled and `PYTHONOPTIMIZE` unset:

```sh
python3 -B verification/reproduce.py --output /tmp/zfc239-replay
```

Choose a new or empty output directory. The driver preserves all archived evidence and writes fresh receipts there. The default runs the complete 239-table runtime proof, taking roughly a few minutes on the recorded environment. It checks JSON success statuses explicitly; a zero process exit code alone is insufficient.

For a short construction/source/boot/local/matrix check that intentionally omits the full runtime replay:

```sh
python3 -B verification/reproduce.py --quick --output /tmp/zfc239-quick
```

For the separate complete predecessor guard proof as well:

```sh
python3 -B verification/reproduce.py --with-guard --output /tmp/zfc239-with-guard
```

The main verification needs only Python's standard library and the files in this archive. It does not compile Lean, download dependencies, or rerun the inherited set-theoretic calibration.

The assembled package was replayed successfully. Its complete fresh receipts are under `evidence/packaged_replay/`, ending in `FULL_239_MATHEMATICAL_REPLAY_PASS`. The original new-machine and predecessor runtime receipts are also retained, together with their referenced case data. The separate full predecessor guard run is recorded in `evidence/selector_guard_certificate.json`.

Build the report with a standard TeX Live installation:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The manifest covers all delivered files other than itself:

```sh
sha256sum -c MANIFEST.sha256
```

## Research beyond the accepted construction

`research/search/` contains the successful C++17 discovery code, its finite window domains, search receipt, and optional regeneration of the source interval data. Those domains were hypotheses for discovery. The final acceptance proof covers every original unbounded instruction case.

```sh
python3 research/search/reproduce_discovery.py \
  --baseline reference/zfc240_old.tm --output-dir /tmp/zfc239-search
```

`research/formalisms/` contains exact three- and four-valued logical countermodels, proofs for an unbounded family of fourth-input substitutions, and eighteen complete-source diagnostic compiler outputs. The logical countermodels include all retained logical rows, GEN, MP, atomic fresh vacuity and IR; they do not assert CP or GIC. The compiler controls use the public 281-state backend and retain its known missing row. They are explicitly not new total consistency machines or transferable subtractions from 240.

The standalone logical checker is `research/formalisms/check_specialization_obstructions.py`. For optional cost regeneration, follow that directory's notes and pass the pinned ProveIt checkout to `measure_specializations.py --repo /path/to/ProveIt`.

Other retained research includes a qualified permutation-quotient obstruction, independently checked interval invariants, a different verified 240-state layout, and an exact source-only NIP specialization whose binary repair is unfinished. See `research/README.md` for scope and commands. These results are supplementary; none is a premise of the chosen 239-state machine's acceptance.

## Incorporation and proof status

A suggested repository destination is `Computability/BusyBeaver/Research/ZFC/candidate-delayed239/`. The existing source calibration and tree identity remain the logical dependencies because the source is unchanged. Preserve the historical 240-state artifacts. `reference/proveit/` contains copied prior source definitions and verification records, with their original historical paths; they are not relabeled as new compilation runs.

The report gives two routes for a future exact-table Lean proof: port the local fold plus its guard, or instantiate the existing runtime framework for the new table and certify complete coverage and startup. Compensated244 remains the smallest closed external Lean consistency endpoint at the pinned checkpoint; this packet adds a smaller ordinary mathematical construction.

The main equivalence is unconditional as a theorem of ZFC. Actual nonhalting follows under consistency of ZFC. Under that assumption Gödel II prevents ZFC from proving the nonhalting statement. For two-sided independence one needs a stronger assumption, such as arithmetical Sigma-1 soundness; bare consistency alone is not asserted to exclude a proof of halting.

See `ATTRIBUTION.md`, `provenance.json`, and `licenses/` for the inherited authorship and exact input identities.

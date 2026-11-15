# Joint decoder forests for PA consistency machines

## Result

No valid machine below 194 working states was obtained. This package supplies
three structurally different 194-state binary, single-tape, blank-start
machines: **PA194ForestR**, **PA194ForestB**, and **PA194ForestX**.

The written theorem for each exact table is

\[
\mathrm{iPRA}\vdash\neg\operatorname{Halt}_{\rm blank}(M)
\leftrightarrow\operatorname{Con}(\mathrm{PA}).
\]

The new part is an exact uniform physical/source simulation with explicit
primitive recursive halting-witness transports. Its absolute PA calibration
uses the supplied **revised AX11H written theorem**, included unchanged and
reviewed in `reference/WRITTEN_CALIBRATION_AUDIT.md`. No new end-to-end Lean
or Rocq verification is claimed.

## Read first

- `report/main.pdf`: complete report, written proof, comparison and all transitions.
- `report/main.tex`: editable LaTeX source, with generated input files alongside it.
- `construction/specifications.json`: the three small source-forest specifications.
- `machines/<name>/machine.tm`: authoritative dense transition tables.
- `proof/clock_certificates.json`: exact source/frame identities and clock coefficients.
- `comparison/comparison_notes.md`: detailed comparison and census boundaries.
- `research/`: reproducible unsuccessful reductions, with finite search bounds.

Every row in a machine file is `state read write direction next_state`.
Start is state 0 with head at coordinate 0 on an all-zero two-way tape.
Working states are 0 through 193. Halt is 194, with no outgoing rows.
Each machine has 388 transition rows; all 194 controls are graph-reachable.

| Machine | State budget | Changed source addresses | Exact blank startup |
|---|---:|---:|---:|
| PA194ForestR | 135 + 66 - 7 = 194 | 449 | 57,922 steps |
| PA194ForestB | 135 + 66 - 7 = 194 | 438 | 58,082 steps |
| PA194ForestX | 136 + 66 - 8 = 194 | 449 | 58,180 steps |

The three closed routine associations are changed jointly; equal decoder
subtrees are shared with the AX emitter. ForestB has a balanced operand
reader. ForestX exposes an additional fold of runtime control 41 into
control 99, the two-increment reader also shared with the AX emitter.
Both controls are charged to the fixed-state budget; this is not a fold
into one of the 66 AX-counted readers. These are active recurring control changes, not unused-row
edits, state renamings or tape reflections.

Each machine has 3,671 source instructions, including 1,107 decrements.
Each decrement contributes a zero and a positive branch, so the independent
literal-row verification checks all 4,778 source outcomes: 4,777 nonhalting
outcomes and one halt outcome. It quantifies over arbitrary natural register values, arbitrary nonnegative
header slack and an arbitrary nonempty finite spare list. The checker
rederives four list lemmas from the literal table and uses no compiler
arithmetic-box oracle. Complete blank tapes and dense/native conjugacies
are also checked.

All three have the same exact affine envelope. If `T` is their startup time,
the sufficient physical clock is `P(k) = T + 9*k*k + 689*k`. For any parent
or child pair, a halting witness `t` for the first becomes `P(t+1)` for the
second. The report proves this in iPRA, including the absorbed halted case.

## Reproduce

Python 3.10+ and the standard library suffice. Do not use `-O`.

```bash
python3 -B verify_all.py
```

This reconstructs each table in a fresh temporary directory, compares all
source and machine artifacts, replays the universal literal checks for the
parent and all three children, inspects source/clock bindings, and tests
novelty. The literal replay is the slow part; the construction itself takes
only a few seconds. No network, repository checkout, external tape input,
search heuristic or Lean installation is required.

To reuse the already run literal certificates while checking their exact
input/output hashes, source closure, clocks and reproducible construction:

```bash
python3 -B verify_all.py --reuse-checked-contracts
```

The resulting receipt explicitly records that mode. It must not be described
as a fresh rerun of the literal symbolic interpreter. To recompute all 548
reference canonical graph forms, add `--recompute-novelty`.
By default, each run writes `verification/release_check.json`; use
`--output PATH.json` to preserve that receipt and save another run separately.

Individual commands:

```bash
python3 -B construction/build.py --output rebuilt
python3 -B verification/check.py rebuilt/PA194ForestB
python3 -B proof/check_clocks.py
python3 -B comparison/check_novelty.py --recompute
```

Build the report from its directory:

```bash
cd report
python3 generate.py
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

## Comparison scope

The pinned ProveIt commit is `7c0bb454cf73c29ca1c385f9fec856ddd236a7cb`.
The scan covers 100 filed packets and six incoming ZIPs, verifies all 15,727
selected tracked payloads against Git blobs, and finds 548 spanning
194-state classes plus two nonspanning 194-control diagnostics. These
include failures and are not 548 calibrated consistency machines.

The 104-design named roster and 43 mechanism groups are included. The joint
forest search tests 250 complete families; 63 pass construction checks, of
which 62 are new and mutually distinct under a broad graph equivalence.
The old graph it recovers is the newest incoming PA194ORH, providing a
positive control. The three released representatives have the additional
independent literal verification and written proof.

The three designs are new even allowing arbitrary spanning roots, state
renaming, tape reflection, global symbol exchange and ignored halt-edge
actions. Symbol exchange is only a stronger novelty comparison, not a
claim about preserving the fixed zero-blank semantics.

## Attribution and limits

The numerical calculus, compiler/runtime infrastructure and absolute
calibration are inherited from the ProveIt PA research and upstream work;
see `PROVENANCE.json`, `licenses/`, and the report references. The new
contribution is the joint forest construction, exact new tables and
uniform weak-arithmetic transport, expanded comparison, and additional
reduction experiments. The unchanged full calibration ZIP is retained,
alongside readable copies of its ten mathematical components.

No negative search proves a 194-state lower bound. Failed or diagnostic
193-state tables are not promoted to results. `MANIFEST.sha256.json` binds
the final release, excluding itself and the mutable replay receipt.

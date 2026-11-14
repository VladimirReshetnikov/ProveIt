# PA-consistency machine comparison and reduction research

**Outcome:** no verified machine with fewer than 196 working states was obtained.
The smallest state count in this archive remains 196. It includes James Chang's
published table and a new 196-state variant with shorter source paths. This is a
research and verification package, not a claimed 195-state
construction. `RESULT.json` records this status in machine-readable form.

## Main deliverables

- `report/pa_tm_research.pdf`: compiled report, including further research questions.
- `report/pa_tm_research.tex` and `report/pa_reverse_translation.tex`: complete LaTeX sources.
- `comparison/`: all nine designated 208-state inputs, the 209/196 bindings,
  source descriptions, manifests, license notices, and a portable exact comparison.
- `sources/BusyBeaver/`: the unchanged tracked publication snapshot of PA196,
  pinned to `407cdc356f6b586635e71ac92be394255f4bfea4`, without Git metadata.
- `verification/lean/`: the standard-library-only physical proof actually rebuilt,
  its startup and coverage logs, and a guarded axiom audit.
- `verification/check_symbolic.py`: the independent Python arbitrary-natural
  symbolic contract checker.
- `alternative196/`: a new 196-state table, source tree, label map, grammar,
  exact blank-start check, and self-contained symbolic checker. This variant
  has not been newly checked by the Lean kernel.
- `experiments/engine196/`: a compact reproduction packet for the 198-state
  source-specialization experiment, including its startup limitation.
- `work/`: experimental search programs and frozen receipts. These are discovery
  tools, not trusted proofs and not accepted sub-196 constructions.

## Findings

1. The nine 208-state tables form exactly two rooted, action-preserving graph
   isomorphism classes (five presentations of A and four of B).
2. Their final saving identifies native roles 172 and 211. Both roles are already
   absent in PA196, so this saving cannot simply be applied again.
3. The specified James Chang PA209 and PA196 tables have 268 common native rows;
   265 agree exactly. PA196 removes 75 old states and introduces 62, a net saving
   of 13.
4. The 58,154-step startup, all 4,959 arbitrary-natural instruction cases, and
   tape/source halting equivalence were freshly rebuilt with Lean 4.35.0.
5. The published arithmetic Lean endpoint explicitly proves
   `PA proves Nonhalt -> Con(PA)`. The report gives a written syntactic argument
   for the reverse direction and states its compilation obligations. This package
   does not claim a new end-to-end Lean proof of the internal biconditional.
6. A new head order `(1,2,3,5,6,4)` and reassociated grammar retain 196 states,
   reduce maximum source-path length from 38 to 36, and pass the exact startup
   and all 4,959 symbolic instruction contracts. This is a layout improvement,
   not a state-count reduction.

## Reproduce the exact comparison

Python 3.10 or later, standard library only:

```sh
python3 comparison/compare_all.py --output comparison/reproduced.json
```

This checks table hashes, canonical classes and bijections, native-label bindings,
the three common-row changes, and source control-flow agreement. The canonical
hashes depend on the documented serialization; the explicit maps are authoritative.

## Reproduce the symbolic instruction checks

```sh
python3 verification/check_symbolic.py
```

Expected output:

```json
{
  "ok": true,
  "contracts": 4959,
  "max_steps": 515,
  "total_steps": 1619679
}
```

The gap and complete register file are symbolic. The finite set consists of
source sites and branch outcomes, not selected numerical register values. The
Python checker is executable evidence; the Lean build below independently
discharges the corresponding universal physical claims.

For the alternative table, run:

```sh
python3 alternative196/verify.py
```

Expected metrics are 196 states, 392 rows, 4,959 contracts, maximum abstract
contract length 497, total abstract steps 1,539,117, and exact startup in 58,154
literal transitions. Its unchanged register engine uses the published macro
contracts. The alternative has no fresh Lean kernel certificate in this archive.

## Rebuild the physical Lean proof

Install Lean 4.35.0 and put `lean` and `lake` on `PATH`. No Mathlib or Foundation
download is required for this smaller physical package.

```sh
cd verification/lean
lake build PA196.CheckCoverage PA196.Startup PA196.ConjugacyReverse
python3 build_batches.py PA196
lake lean Audit.lean
```

The batch script limits simultaneous coverage modules. The guarded audit accepts
only the exact axiom lists shown in the report; an admitted proof changes the
output and fails the guard. The physical dependency closure has 308 upstream
modules, plus the added audit. Build caches are deliberately omitted.

This is a fresh build of the *physical* machine/source equivalence, not a fresh
build of the full arithmetic-independence development. Instructions for that
larger upstream build remain in `sources/BusyBeaver/docs/reproduction.md`.

## Compile the report

With a normal LaTeX installation providing the packages named in the preamble:

```sh
cd report
pdflatex -interaction=nonstopmode -halt-on-error pa_tm_research.tex
pdflatex -interaction=nonstopmode -halt-on-error pa_tm_research.tex
```

## Optional experiments

For the fixed-table searches, run the scripts in `work/optimize196` or
`work/shared_router` from their own directories. `core.py` locates the pinned
source relative to the archive root. Generated search outputs may overwrite
their frozen receipts; use a copy of the archive when experimenting.

Some layout experiments additionally require NumPy/SciPy, NetworkX, or HiGHS.
They have heuristic stopping limits. Their numerical solver bounds are not
formal lower bounds on Turing-machine state complexity. The report explains
which proposed transformations failed and why none is delivered as a sub-196
machine.

The 198-state register-6 specialization is only a runtime experiment from
supplied source frames. It passes 4,956 symbolic contracts, but its blank startup
did not reach a calibrated seed within 1,000,000 steps; it is not accepted as a
blank-tape consistency machine.

## Provenance and licenses

Original publication sources and their license notices are retained unchanged.
The `comparison/licenses` directory retains the relevant ProveIt and upstream
notices. New research scripts and prose in this package may be reused under the
MIT license in `LICENSE.research`; this does not replace any upstream notice.

No repository was modified or published by this investigation.

`SHA256SUMS` records the SHA-256 of every other file in the archive.

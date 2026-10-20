# Research experiments and exact verification scope

**No experiment in this directory is an accepted machine below 225 states.**
The accepted positive machine is `../machine/k225_dn.tm`; the full replay and
logical calibration belong to the main packet. Larger or rejected experimental
tables are retained as reproducible research inputs.

## Directory map

| Directory | What it contains | Strongest stated scope |
|---|---|---|
| `theory/` | Alternative logical bases, parameter/selector permutations, canonical equality vacuity, exact source reconstruction | Full DN4 source/formula proof; measured sources and literal decoder contracts for larger variants |
| `proof_audit/` | Inductive register certificate, NIP specialization/counterexample, auxiliary Rocq proofs, canonical equality comparison | Unbounded ordinary source invariant; exact finite rejection examples; narrowly scoped kernel theorems |
| `decoder/` | Restricted tape windows, fixed/offset/tag screens, open source rotations, seed-relative runtime verifier | Full seed-relative DN4 replay; bounded discovery screens; representative-only probes of other layouts |
| `state_folds/` | C++ neutral-row and one-helper searches, retained enhanced-domain log | Exhaustion of the specified finite state-pair/row/helper family |
| `scanner/` | Targeted short-scanner failures and conditional runtime/blank-start diagnostics | Rejection evidence and explicitly conditional primitive contracts |

The separate READMEs, JSON scope manifests, and receipts explain the boundaries
of each result. A completed numeric source proof does not establish a smaller
binary table; internal prefix contracts do not establish the entire interpreter
runtime; a finite counterexample can reject a table even after many other cases
passed.

## Retained dependencies

Run the main replay once so that it extracts the pinned original archive. For
the decoder and scanner scripts that use the inherited verification engine,
set the explicit dependency path:

```sh
export ZFC_BASELINE_PORTABLE=/absolute/path/to/OUT/inherited/K225_Construction_2026-10-19/portable
```

No inherited source is modified. The standalone theory experiment launcher
takes explicit `--baseline`, `--builder`, `--dag`, and `--dn4` arguments instead;
its own selected inputs are already retained under `theory/`.

## Recheck the selected theory artifacts

From `theory/`:

```sh
python3 -B scripts/verify_selected_results.py
```

This checks the local manifest, selected source metrics, exact 225-state DN4
source reconstruction, and the literal state counts of larger probes. It does
not silently promote a probe to a complete consistency machine.

## Reproduce the restricted-domain one-helper search

From `state_folds/`, with a C++17 compiler:

```sh
c++ -O3 -std=c++17 neutral_domains.cpp -o /tmp/zfc_neutral
c++ -O3 -std=c++17 helper_domains.cpp -o /tmp/zfc_helpers

/tmp/zfc_neutral ../../machine/k225_dn.klabels.tm 6 6 65 65 \
  ../decoder/receipts/dn4_seed_precise_windows.txt > /tmp/zfc_neutral_rows.txt

/tmp/zfc_helpers ../../machine/k225_dn.klabels.tm 6 6 65 65 \
  /tmp/zfc_neutral_rows.txt ../decoder/receipts/dn4_seed_precise_windows.txt \
  > /tmp/zfc_fold_candidates.txt 2> /tmp/zfc_fold_search.log
```

The recorded run uses 610 neutral helper patches and 57,324 working-state
windows (the projection also records one halt-state window). It exhausts all
25,200 unordered state pairs and 45,158,400 retained-row choices, tests
747,955,300 helper combinations, makes 2,704,637,364 context checks, and reports
zero candidates. Both local matching blocks are bounded by 65 transitions.
This result is not a global lower bound or proof of irreducibility.

The two C++ files adapt the retained K225 discovery programs to normalized start
label 0. They are untrusted discovery tools. Candidate correctness must come
from a fresh full runtime proof, source semantic comparison, and exact startup.

## Recheck the register invariant and rejected NIP patch

From `proof_audit/`:

```sh
python3 -B portable_seed_invariant.py ../../machine/sites.json \
  --verify dn4_seed_invariant.json --output /tmp/zfc_seed_invariant.json

python3 -B verify_nip_rejection.py ../../machine/k225_dn.klabels.tm \
  --output /tmp/zfc_nip_rejection.json
```

The first command proves closure of an abstraction of *unbounded* registers
from the calibrated seed. The second reproduces a complete finite tape
counterexample: an intended increment of register 8 becomes a no-op, and the
patched table also loses its inherited startup.

## Interpreting the open-rotation and scanner work

Open source rotations compare the complete guarded control graph. The initial
scan considered 226 moves: 172 preserve that graph, 57 pass the internal prefix
and zero-run screens, and 17 yield 225-state layouts. Sixteen passed the 32-case
representative primitive probe; this is explicitly not a complete runtime proof.

The scanner proposal removes one state, but the retained source has paths with
six consecutive zero bits. A conditional runtime check can exclude those paths
and prove all remaining primitive cases, but that does not establish the whole
machine. The blank initializer also contains a seven-zero gap that the shortened
scanner misclassifies. Any successful route must fix **both** source/runtime
coverage and startup. Exact receipts and further scope limits are retained with
the relevant scripts.

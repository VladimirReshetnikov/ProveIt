# Reproduction guide

## Portable component suite

Requirements: Python 3.12 was used here; a recent Python 3 supporting strict zip and modern type syntax is needed. The default suite uses only the standard library. Run with assertions enabled; never use python -O.

    python3 verify_manifest.py
    python3 run_portable.py

The runner copies research_sub246 into a newly created portable-runs/<timestamp>/research_sub246, executes the listed generators and independent audits there, and records all stdout/stderr and exit statuses. This allows source files that emit their own JSON to run without modifying delivered evidence. The suite stops on a genuine command failure. A table-hash change is reported separately from expected timing/log changes. No input is a ZFC refutation; successful controls and negative endpoints test the checker interfaces.

To select a subset, use:

    python3 run_portable.py --list
    python3 run_portable.py --only copy,comparators,logic

The default does not repeat all expensive bounded source searches, install solvers, or compile Lean/Coq. It validates native component contracts and high-level algorithms to the extent described by their tests and accompanying proofs. Tests do not replace unbounded invariants.

## Pinned source-dependent experiments

The package deliberately omits the 1.2 GB full source tree, repeated recovered packets, compiled solver installations, and several large regenerable diagnostics. A source-dependent script that needs these should not be run against the tiny source subset as if it were complete.

First obtain a separate checkout of the exact pin, for example:

    git clone --filter=blob:none https://github.com/VladimirReshetnikov/ProveIt.git /path/to/ProveIt
    git -C /path/to/ProveIt checkout --detach 7ba1598461c6e485c5aeb8f673c0b1d571f8012b

Then prepare a fresh scratch project (no network access is performed by this helper):

    python3 prepare_source_experiments.py --upstream /path/to/ProveIt --output /path/to/new-work

The helper verifies HEAD, copies this package into the new work tree, replaces its tiny source subset with a symlink to the supplied checkout, and recovers sources 63--67 from the exact pinned placement manifests by git show. It verifies that every recovered target stays inside the new work tree. It never writes to the upstream checkout. Source experiments may generate local outputs; run them only in the prepared copy.

From /path/to/new-work, useful reproducible checks include:

    python3 research_sub246/verification/audit_joint246.py
    python3 research_sub246/context_folds/check_reuse_control.py
    python3 research_sub246/context_folds/verify_deeper_entry_guard.py
    python3 research_sub246/arithmetic_core/prove_borrowed_tail.py --borrowed 126
    python3 research_sub246/machine_encoding/check_borrowed_tail_collision.py
    python3 research_sub246/logical_routes/prefix_helper_correspondence.py

The last source experiments may expect attributed Wade backend files already present in machine_encoding. Their scoped notice is notices/LICENSE.Wade. The recovery driver in the original project used the same pinned placement manifests, not third-party instructions.

For optional synthesis, use a dedicated virtual environment. Historical detector searches used python-sat 1.9.dev16 and z3-solver 5.3.1.0. Finite-dictionary optimization uses SciPy's MILP implementation. Exact command-line options and terminal statuses are retained in each result JSON. A newer solver can differ in runtime, branch order, or timeout behavior. UNKNOWN remains inconclusive. To regenerate C++ enumerations, compile the included source with a standard C++17 compiler rather than using an unverified binary from another machine.

## Report rebuild

The report uses standard LaTeX packages: geometry, lmodern, microtype, amsmath/amssymb/amsthm, booktabs, longtable, enumitem, xcolor, hyperref, fancyhdr, and listings. In a configured TeX Live installation:

    pdflatex -interaction=nonstopmode -halt-on-error sub246-research.tex
    pdflatex -interaction=nonstopmode -halt-on-error sub246-research.tex

The PDF was rendered and visually reviewed before delivery. The PDF is the delivered snapshot; different TeX versions may shift line/page breaks. No proof-assistant compilation is implied by a successful PDF build.

## Proof-assistant boundary

verification/TransferTheorem.lean is an uncompiled generic composition draft using the pinned runtime interface. At experimental pin7ba1598 the exact246 Lean endpoint was conditional on actual-tree coverage. Later upstream commit69c976afc6050b14e2ce7c855a77d4e6765fcf68 closes BinaryPrefix246.nonhalting_iff_zfc_consistency without startup/coverage premises; its retrieved endpoint is included and was read, but no local Lean build or full prerequisite rebuild was run here. All experiments remain pinned to7ba1598. Original Jeff Coq verification recommends Coq 8.20.x and has its own complete dependency closure. No new Lean or Coq kernel pass is claimed by this package.

## Separate successful 245-state construction

The current overall result is affirmative, through the separately supplied and independently audited 245-state archive. Its reproduction is described in AUDIT245_REPRODUCE.md. It is distinct from the native component suite and the source-dependent alternative experiments described above. The minimal baseline audit dependencies are now included as an explicit exception to the omission of full recovered/source trees.

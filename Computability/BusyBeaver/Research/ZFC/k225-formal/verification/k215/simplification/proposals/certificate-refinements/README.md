# Verified certificate refinements for K215

Research and integration packet, 21 October 2026.

Repository snapshot:
`53269bcab1efc0f82d3022645bd7cf0c22d84959` of
[VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt).
The research includes all seven ZIP proposals in `docs/incoming` at that pin.

## Results

1. **Exact source proof with balanced certificate lookup.**
   `Source215Balanced.p215_dagPerm_balanced` proves, for every register file
   `R`, `rm_halts p215 ([], R) <-> rm_halts dagPerm ([], R)`.
   The new tree checker is proved equal to the inherited ordinary checker.
   The exact 2,240-entry certificate gives 54,514 lookup-node visits versus
   5,018,706 with list indexing. This is a count of one component, not a
   92-fold runtime claim. A single local timing was lower; tree construction
   adds cost, so no whole-build speedup is claimed.
2. **One generic finite checker for M124, FM215, and provider-125 M125.**
   The checked theorem gives arbitrary-tape halting equivalence with the exact
   primary K215. Three literal instances use the same two-clause invariant.
   M125 native and dense tables are supplied. Provider 125 was already
   suggested in the M124 incoming note; no novelty claim is made for the idea.
3. **Concrete zero-credit enumeration theorem.**
   `CantorCredit.v` proves the actual Cantor encoding and decoder, the strict
   NIP-to-DROP occurrence injection, and protected credit for the literal
   increasing raw-code schedule. The mathematical injection is prior work;
   the new contribution closes the concrete codec and scheduler hypotheses.
4. **No 214-state machine found.**
   A reproducible restricted fold search covered 21 tables, 155,277
   pair/table combinations, and 133,827,040 replacement-action checks.
   No complete fold passed. This supplies no lower bound and is not a count
   of distinct complete machines.

All delivered machines have **215 working states**, a separate halt, one
binary two-way tape, L/R moves, and initialization included.

## Read first

`report.pdf` is the complete report; `report.tex` and `sections/*.tex` are its
editable source. The report distinguishes existing proposals, new compiled
results, finite corroboration, and future integration work.

| Directory | Purpose |
|---|---|
| `balanced_lookup/` | Generic lookup refinement, exact source theorem, minimal inherited dependencies, measurements and compiler receipts |
| `marker_certificate/` | Generic table checker, three compiled instances, literal tables and finite audits |
| `zero_credit/` | Concrete scheduler theorem, candidate comparison, incoming inventory and independent marker review |
| `state_search/` | Restricted search implementation, controls, counts, provenance and explicit-table inventory |
| `evidence/` | Independent review of the balanced checker and measurements |

## Verification scope

The new formal modules were compiled with **Coq 8.18.0 / OCaml 4.14.1** and
their selected assumption reports are closed. Recursive `coqchk` passed for:

- the generic `BalancedBisim` module and its dependencies;
- the concrete `MarkerInstances` module and its dependencies;
- `CantorCredit`.

The exact balanced source theorem was kernel-checked during compilation;
it was not included in the separate recursive generic audit.
No complete 237-source Rocq endpoint or full Lean endpoint was rebuilt here,
and the maintained Rocq 9.1.0 lane was not replayed.

The marker instances use a native arbitrary-tape model. Their compiled bridge
to ProveIt's dense/zipper endpoint remains integration work. The concrete
credit theorem is about the exact arithmetic schedule, not the physical
ZC215 machine. These boundaries are not filled by the finite startup checks.

## Reproduce

Integrity and recorded source bindings, no external packages:

~~~sh
python3 verify_packet.py
~~~

PDF (standard LaTeX distribution with packages listed in `report.tex`):

~~~sh
python3 build_pdf.py
~~~

Formal results, using fresh output directories and Coq 8.18.0 on PATH:

~~~sh
python3 balanced_lookup/reproduce.py --output /tmp/k215-balanced-fresh
python3 balanced_lookup/lookup_metrics.py
python3 marker_certificate/build.py --out /tmp/k215-marker-fresh
python3 marker_certificate/verify.py --output /tmp/k215-marker-finite.json
python3 zero_credit/build.py --out /tmp/k215-credit-fresh
~~~

Add `--check-generic` to the balanced runner for its recursive generic audit,
or `--benchmark` for the ordinary baseline. The other two proof drivers run
recursive audits. They serialize compilers with a common temporary lock.
The new formal results require no complete repository checkout, Mathlib,
network access, or binary proof cache. The original Rocq 9.1 dependency
source is retained with a compatibility shim for the tested 8.18 lane.

The search requires Python 3, a C++17 compiler, and the pinned checkout:

~~~sh
python3 state_search/run_search.py \
  --repo /absolute/path/to/ProveIt --out /tmp/k215-search-fresh
~~~

Its bounds and exclusions are in `state_search/STATE_SEARCH.md`.

## Integration recommendation

Keep primary K215 and its public theorem names. Reuse the incoming ordinary
one-sided source proof and compact certificate; adopt balanced lookup behind
`p215_dagPerm`, update the maintained generator, and rebuild `Correct215` and
`CorrectDense215` with fresh assumption reports. Combining balanced storage
with the incoming 1,426-entry normalized certificate is a further step, not
a result checked here.

For another 215-state endpoint, M124/FM215 have the smallest new marker
invariant; CM215 may integrate faster because incoming work already provides
its concrete dense/Core bridge. ZC215 has the cleanest independent scheduler
argument, now made concrete in the supplied proof.

## Provenance and licensing

See `NOTICE.md`, the top-level `LICENSE`, and the preserved notices under the
formal packages. New code and report material may be incorporated under
ProveIt's MIT No Attribution terms. Inherited materials retain their own
notices and licenses. The top-level `manifest.json` covers all distributed
files except itself; subpackage manifests and compiler receipts are retained.
Compiled objects and PDF intermediates are intentionally omitted.

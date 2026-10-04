# Independent reduced POWER module audit

Read `AUDIT.md` for the mathematical verdict, scope, proofs, and limitations.

`check_independent.py` is a standalone Python 3.9+ standard-library checker. Only this freshly authored and inspected checker was executed. The original packet and its author script remain read-only; no Lean, source-author scientific code, counter interpreter, or physical simulation was executed.

Reproduce:

    python3 check_independent.py --source /path/to/positive-power22-reduction-20261004 --out /path/to/new-evidence

The successful local run is recorded in `run.log` and `evidence/results.json`. The evidence directory also contains all eight independently expanded polynomials and a complete source hash/mode/mtime snapshot. Before/after shell snapshots independently confirm preservation.

Verdict: all scoped module equivalences, reconstructions, exact degrees, composition counts, and infinite-fiber claims pass. The all-exponent assertion retains the exact pinned Pell theorem dependency. No optimality, finite-fold, or unbounded-horizon single-polynomial claim is made.

# Odd-helper direct quartics

The three selected equations are centered307, centered308 and centered310.
Every unknown is an unrestricted integer and every equation is the sum of
squares of the complete quadratic residual list in equation.json. Its full
collected coefficients are in expanded_polynomial.json.

| Directory | Variables | Rows | Degree | Terms | Height |
|---|---:|---:|---:|---:|---:|
| centered307 | 307 | 211 | 4 | 22532 | 394412 |
| centered308 | 308 | 212 | 4 | 5364 | 195962 |
| centered310 | 310 | 214 | 4 | 5612 | 128446 |

PROOF.md gives the full new unbounded proof. full_proof.tex is its editable
LaTeX conversion; section.tex is the concise report section. Source arithmetic,
square-shell recoding, native calculus, and named logical calibrations are
retained in source/. No consistency or global minimality claim is made, and
this is not a newly kernel-checked end-to-end theorem.

The novel result is the exact odd-helper composition and its literal completed
endpoints. The prior odd-quotient idea, cofinal choices, self-radix and support
products are explicitly credited. Source131's 324-variable quartic has fewer
rows (208), so variable/support improvements are not all-metric domination.

Conservative proof checkpoints odd_t and odd_y are retained. self_radix,
self_radix_qf and self_radix_min are the exact uncentered parents of the three
selected charts. Every raw transformed source, all graph changes, Horn edits,
monic restoration steps and translations are supplied. The original source
and incoming manuals are provenance, not an instruction to execute remote code.

Offline reproduction with standard-library Python:

    python -B check.py > CHECK_NORMAL.json
    python -B -O check.py > CHECK_OPTIMIZED.json
    python -B check_diagnostics.py > DIAGNOSTICS.json
    python -B check_inventory.py > CACHE_INVENTORY_CHECK.json
    python -B -O check_inventory.py > CACHE_INVENTORY_CHECK_OPTIMIZED.json
    python -B reproduce.py --receipt REBUILD_NORMAL.json
    python -B reproduce.py --optimized --receipt REBUILD_OPTIMIZED.json

Each rebuild first copies the complete input tree without Python bytecode or
cache directories, then runs only from that clean copy. No cache path may
appear in the source dependencies. seal.py regenerates source-pin and release
inventories with the same recursive exclusion, while rejecting changed
authentic source files. It is a maintainer utility, not a required proof step.

Use receipt destinations outside a sealed release to preserve its inventory.
The independent checker imports no producer and verifies every coefficient,
18 full power lowerings, 15 primary norms, 11 residue ideals, graph privacy,
frame coverage, Horn maps, monic restorations, and affine charts. Its eight
corruption controls must be rejected. Finite signed-helper diagnostics are
explicitly finite tests, not proofs of consistency or unbounded lemmas.

No network access, repository writes, machine simulation, consistency search,
SymPy, or theorem-prover execution is needed to rebuild these equations.

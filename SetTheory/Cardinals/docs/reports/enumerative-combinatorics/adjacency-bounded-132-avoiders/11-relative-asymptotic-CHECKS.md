# Exact finite checks

From the package directory run:

    python3 checks/verify_good_subclass.py
    python3 checks/independent_replay.py

Both use only the Python standard library.

The primary verifier reconstructs the relaxed parser for all 132-avoiders
through size nine. It checks exact squared-envelope counts, Catalan
factorization for each spine shape, the restricted-decoration product,
retained cap inequalities, and the marked deletion/reconstruction of long
append runs. It writes good_subclass_results.json beside itself. Expected
totals: 6917 parser round trips; 5766 shape factorizations; 17298 restricted
factorizations; 53563 good cap checks; 16932 marked deletions; 405 rows.
The ordered row hash is
7a450479b7f774cf288fc04ed287b144d09cff2c62b274aaacbbbadbbe73cdf7.

The second verifier is a separately implemented permutation-level replay
through size ten, with no imports from the primary verifier or model.py.
It checks 50 envelope equalities, 450 bad-family parameter cases, and
126565 retained cap inequalities. Its output is saved in
independent_replay_results.txt.

model.py is inherited verbatim and credited in SOURCES.md. These finite
regressions check combinatorial bookkeeping, not the uniform local limit,
its asymptotic range, or an effective convergence threshold.

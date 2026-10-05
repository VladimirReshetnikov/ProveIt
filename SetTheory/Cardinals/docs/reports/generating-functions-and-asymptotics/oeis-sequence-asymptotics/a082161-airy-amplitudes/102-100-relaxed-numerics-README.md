# Optional numerical diagnostics

These scripts reproduce exploratory numerical checks reported in the article. They are separate from the fail-closed exact certificate in `../checks/` and are not needed for any mathematical proof or exact-suite acceptance.

Dependencies: Python 3, mpmath, SymPy; the two spectral scripts also require NumPy and SciPy. The original recorded diagnostic runs used exact-integer dynamic programming through n=3000 followed by 90-digit mpmath evaluation, and floating-point tridiagonal eigenvalue computations through n=100000. The standalone source implementations are retained here, with an explicit bound on the optional dynamic-programming argument. Their diagnostic outputs and amplitude extrapolations have no rigorous interval error bounds.

Run from this directory:

    python check_dp.py 3000
    python analyze_numerics.py
    python check_jacobi.py
    python compute_canonical_amplitude.py

The first command regenerates exact integer triangle rows in memory and writes sampled high-precision decimal diagnostics to `exact_dp_3000.json`. Despite that legacy filename, the JSON is not an exact integer archive. It includes elapsed runtime, which is not deterministic. The second command uses those checkpoints for inverse-error calculations and numerical amplitude extrapolation. Archived versions of the JSON diagnostics are in `../checks/diagnostics/`; these originals are not overwritten by these commands.

`check_jacobi.txt` and `compute_canonical_amplitude.txt` are the recorded spectral/product outputs. Reproducing them is optional and may be substantially more expensive than the exact suite. Floating-point output can vary slightly across numerical-library versions. Neither matching these files nor observing convergence certifies any decimal digit of gamma. In particular the raw canonical product converges slowly: its n=3000 approximation is still far from the limiting estimate.

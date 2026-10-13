# Provenance of the finite kernels

`base.py` and `base_verify.py` are unchanged copies of the discovery and
independent verification kernels in the preceding ProveIt incoming package
`ProveIt_Dual_Forest_Normalization_2026-10-12.zip`, under `code/forest_search/`.
They are vendored to make this research module standalone and avoid changing
the predecessor's import conventions. The independent verifier imports no
producer code.

The repository checkpoint is `c6d0ec8aa0b6308310ab6c081ba29d8bc363ede5`.
The repository's MIT No Attribution license is retained in the delivered
package's root `LICENSE`. The incoming package and its results are credited
as prior work in the article; these two kernels are not claimed as new work.

`solver.py` and `nonlinear.py` implement the new exceptional-column,
Boolean/ideal, and deterministic-width algorithms. See the article for the
proofs, exact scope, and resource/randomness conventions.

## Exact copied-file hashes

- `base.py` from `code/forest_search/dual_forest_search.py`: `d93fc23c4eab48c44f858d5408f2017e191185625f70c7c592d6d5edeaf658b8`
- `base_verify.py` from `code/forest_search/dual_forest_verify.py`: `8bfdaa4850605ada8b20b45e473548984c9314b7393dca8b27193266da6f8783`

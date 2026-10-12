# Exact tail reconstruction certificates

This folder is self-contained apart from Python and the explicitly listed software dependency. It contains no binaries and requires no network access at replay time.

## What is proved

- **Smaller order ten:** every `(p,q)=(10,2b)`, `b>=6`, has the optimal first-`q` formal coordinate rank. Two inherited source theorems already cover every parameter except `b=962`. The missing original determinant is `15578 (mod 65537)`; the retained five-square determinant is `60407 (mod 65537)`.
- **Smaller order twelve:** every `(p,q)=(12,2b)`, `b>=7`, has optimal first-`q` rank. The article proves the infinite range `b>=11520` analytically. The finite certificate covers **every one of the 11,513 integers `7<=b<=11519`**, and every recorded determinant residue modulo `65537` is nonzero.

These are rational coefficient-rank statements in the source's formal coordinate space. They do not assert arithmetic independence of zeta values. The unrestricted unequal-order conjecture and the entire gap-six family remain open.

## One-command replay

Requirements: Python 3.10 or later and SymPy 1.12 or later. SymPy is used for the independent order-ten check; the complete independent order-twelve replay uses only the Python standard library.

From this folder:

```sh
python run_tail_checks.py
```

The default command checks the hashes of all included inherited source inputs, runs the primary order-ten certificate, runs its independent Padé-row/exact-Bernoulli check, and independently replays **all 11,513** order-twelve cases.

For the additional independent C++17 scan and optional sharper coefficient bound:

```sh
python run_tail_checks.py --full
```

A C++17 compiler named `c++`, `g++`, or `clang++` must be on the executable search path. The executable and freshly generated C++ residue list are created in a temporary directory and removed after the replay. They are never installed into this package. The freshly generated list is compared in full with the published certificate. The entry point verifies that the published order-twelve residue file is unchanged.

The command writes `run_tail_checks.json`, or `run_tail_checks_full.json` when `--full` is selected. Individual scripts refresh their own result receipts; diagnostic timings can change. Recorded mathematical outputs and the complete residue list are checked for preservation.

## Independent algorithms

The complete C++ order-twelve verifier uses the triangular Bernoulli recurrence, finite differences at each integer parameter, and modular Gaussian elimination. It uses the original source matrix for `7<=b<=11`; the six-square retained matrix is valid for `b>=12`. It independently checks the original-versus-retained determinant relation, including the full multiplier, at all `12<=b<=32`.

The complete Python order-twelve verifier uses different computational routes:

1. Newton inversion of `(exp(t)-1)/t` produces `B_n/n!` directly. Polynomial multiplication uses exact integer Kronecker substitution, with a checked bound that prevents carries between coefficient blocks; it does not use floating-point FFTs.
2. Globally computed integer Newton-coefficient polynomials and factorial-cancelled entries construct the six-square matrices.
3. A division-free subset Laplace expansion computes each determinant.
4. Every residue is required to be nonzero, and the complete ordered list must agree with the independent C++ certificate. The final power-series inverse is checked through degree 23039.

No implementation infers the infinite theorem from sampled determinants. The analytic threshold and complete finite certificates are separate components of the proof.

## Core files

| File | Role |
|---|---|
| `complete_p10.py`, `complete_p10.json` | Primary exact order-ten certificate |
| `verify_p10_independent.py`, `verify_p10_independent.json` | Independent Padé-row and exact rational Bernoulli check |
| `complete_p12.cpp`, `complete_p12.json` | Primary complete order-twelve certificate; the JSON contains all 11,513 residues |
| `replay_p12_independent.py`, `replay_p12_independent.json` | Independent complete standard-library Python replay |
| `coefficient_norm_bound.py`, `coefficient_norm_bound_a6.json` | Optional sharper factor-product bound; also provides globally computed Newton polynomials to the Python replay |
| `order_twelve_example_12_18.json` | Optional exact rational identity data for `(p,q)=(12,18)` |
| `provenance_inputs/manifest.json` | Pinned inherited-source names and hashes |

The article's elementary `2^512` coefficient bound and `2^-779` initial domination estimate do not depend on the optional sharper norm output.

## Included inherited source dependencies

Every included source file is preserved byte for byte; `provenance_inputs/manifest.json` records its SHA-256 hash and the repository pin `da2792fc9cc8ef19c6a314be6c65e1437fbdc66b`.

1. **Alternating Tails and Spectral Defects.** Theorem `rt:rank10` in `sections/07_rank_refinement.tex` proves every `b>=6` outside `962 mod 2048`. Its full order-ten and order-eight polynomial certificates, direct base-case results, independent verifier, and original proof text are included.
2. **Quartic Spectral Reconstruction.** `sections/03_eventual_rank.tex` contains the source-to-retained determinant normalization, its Padé proof, the general leading homogeneous factorization, and the eventual nonvanishing argument. Its exact `a=5` threshold input/output and general normalization verifier are included. These support the inherited threshold `B5=1920` used to complete order ten.
3. `sections/08_research.tex` of the Quartic report explicitly requests complete order-ten and order-twelve families in research question R1. The article resolves both specified tasks; R2, uniformity in every `a<b`, remains open.

The inherited symbolic certificates can also be replayed separately from this folder:

```sh
python provenance_inputs/ProveIt_Alternating_Tails_Spectral_Defects_2026-10-11/verification/verify_rank_refinement.py
python provenance_inputs/ProveIt_Quartic_Spectral_Reconstruction_2026-10-11/verification/eventual/eventual_threshold.py 5 --output inherited_threshold_replay.json
python provenance_inputs/ProveIt_Quartic_Spectral_Reconstruction_2026-10-11/verification/eventual/verify_general_normalization.py
```

The first inherited replay can take several minutes. Running an inherited script may refresh its original receipt and therefore change a file protected by the provenance manifest; use a copied verification folder if preserving the byte-for-byte source snapshot is desired. This does not affect the new default/full replay, which only reads those inherited files.

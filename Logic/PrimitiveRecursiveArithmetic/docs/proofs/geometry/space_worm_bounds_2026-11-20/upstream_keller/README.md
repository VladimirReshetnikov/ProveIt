# Improved bounds for universal convex covers of unit arcs

Code, Lean 4 proofs, and compressed certificates for the paper
["Improved bounds for universal convex covers of unit arcs"](https://arxiv.org/abs/2609.21968)
(arXiv:2609.21968). The improved bounds are `0.239 ≤ α ≤ 0.2463322372…`, where `α` is the
infimum area of a convex universal cover of unit planar arcs.

Numerical checks use `decide +kernel`, with no `native_decide`.
The final theorem `MoserWorm.bounds` depends only on `propext`,
`Classical.choice`, and `Quot.sound`.

## Files

- `MoserWorm/`: shared lemmas, lower and upper proofs, and certificate checkers.
- `scripts/`: separate `lower/` and `upper/` commands, with shared helpers in `common.py`.
- `certificates/`: compressed lower and upper certificates with manifests and checksums.
- `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`: pinned Lean and mathlib dependencies.

## Requirements and setup

Linux, CPython 3.9 (tested with 3.9.25), `venv` and `pip`, Git, `curl`, and
Lean via `elan`. Lower bound certificate generation also requires GCC. Lean 4.33.1 and mathlib are pinned.

Run these commands from the repository directory:

```sh
python3.9 -m venv build/venv
source build/venv/bin/activate
lake exe cache get
```

## Verify the supplied certificates

```sh
python scripts/lower/verify.py --jobs N
python scripts/upper/verify.py --jobs N
lake build MoserWorm
```

Each verifier checks its bound and audits its axioms independently.
The final Lake command combines the two bounds.
`--jobs N` sets a maximum number of workers.

## Regenerate certificates

To generate fresh certificates:

```sh
python scripts/lower/generate.py --jobs N

# Upper bound generation script has a few extra dependencies (numerical packages)
python -m pip install -r requirements-upper-search.txt
python scripts/upper/generate.py --jobs N
```

To re-verify the freshly generated certificates:
```sh
python scripts/upper/verify.py --certificates build/certificates/upper --jobs N
python scripts/lower/verify.py --certificates build/certificates/lower --jobs N
lake build MoserWorm
```

The numerical Python packages are needed only for upper generation.
Use `--output PATH` to choose another destination.
Verification logs land in `.lake/logs/`.

## Timings

Measured on Linux with an AMD EPYC 9R14, 64 logical CPUs, and 128 GiB RAM.

| Step | Jobs | Wall time |
|---|---:|---:|
| Lower verification and audit | 50 | 3h 56min |
| Upper verification and audit | 12 | 59min |
| Lower generation | 64 | 1h 24min |
| Upper generation | 16 | 2min |
| Combined theorem and audit | — | 27sec |

Total: **4h 55min** to verify, or **6h 21min** including generation.

## Citation

Paper: [arXiv:2609.21968](https://arxiv.org/abs/2609.21968),
[doi:10.48550/arXiv.2609.21968](https://doi.org/10.48550/arXiv.2609.21968).

```bibtex
@misc{keller2026arcs,
  title         = {Improved bounds for universal convex covers of unit arcs},
  author        = {Keller, Ethan},
  year          = {2026},
  eprint        = {2609.21968},
  archivePrefix = {arXiv},
  primaryClass  = {math.MG},
  doi           = {10.48550/arXiv.2609.21968},
  url           = {https://arxiv.org/abs/2609.21968}
}
```

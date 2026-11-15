# Euler's rotation theorem and Rodrigues' formula in iPRA

The main report is `euler_rodrigues_ipra.pdf`; its LaTeX source is
`euler_rodrigues_ipra.tex`, with two included `.tex` sections.

## Mathematical outcome

The unrestricted classical exact-unit-axis assertion for arbitrary real
rotation matrices is not uniformly constructively provable in the chosen
PR-Cauchy-name interpretation. The report proves this by an explicit LLPO
reduction and a non-realizable first-order arithmetic consequence.

It also gives complete human-readable proofs of:

1. Rodrigues' formula for a supplied unit axis and angle, including an
   explicit finite-sum construction of sine, cosine, and an angle representative.
2. The unconditional exact Euler theorem for rational proper orthogonal
   matrices, with a rational nonzero axis and an explicitly normalized PR name.
3. Exact Euler and Rodrigues reconstruction for real names with a supplied
   numerical bound separating the rotation from the identity; half-turns
   are included.
4. Uniform approximation by an axis-and-angle rotation at any requested
   precision, without a gap promise or a claim that the axes converge.
5. Exact unit-quaternion data for every represented real rotation,
   including the identity, where the vector part is permitted to vanish.

All positive theorems are accompanied by explicit primitive-recursive
operations, precision bounds, and a quantifier-free induction audit.
Represented-real statements are schemas for each fixed PR input family;
they do not postulate a universal total PR program evaluator.

## Contents

| File or directory | Purpose |
| --- | --- |
| `euler_rodrigues_ipra.pdf` | Complete research note |
| `euler_rodrigues_ipra.tex` | Main LaTeX source |
| `trigonometric_bridge.tex` | Finite-sum radian-angle construction, without FTC |
| `formalization_and_audit.tex` | iPRA audit, Lean completion path, references |
| `lean/RodriguesKernel.lean` | Uncompiled finite algebra prototype, without `sorry` or new axioms |
| `lean/ObjectLanguageBoundary.lean` | Actual ProveIt PR interfaces and transport of a supplied derivation |
| `lean/FORMALIZATION_PLAN.md` | Detailed implementation milestones |
| `lean/FORMALIZATION_STATUS.txt` | Exact formalization status and remaining obligations |
| `python/rotation_certificates.py` | Exact rational extraction and certificate verification |
| `python/verify.py` | Exact tests, normalization intervals, finite-precision branches |
| `python/verify_polynomials.py` | Exact polynomial checks with SymPy |
| `python/verification_*.json` | Recorded executable results |
| `sources/manifest.json` | Pinned repository and external source provenance |
| `verification/` | Build, review, and PDF validation information |
| `build.sh` | Reproducible PDF build, with minimal TeX initialization fallback |
| `SHA256SUMS` | Checksums of the packaged files |

## Reproduce

From this directory:

```sh
python3 python/verify.py
python3 python/verify_polynomials.py
bash build.sh
```

The first script uses Python's standard library. The symbolic checker needs
SymPy (see `python/requirements.txt`). The report uses standard TeX Live
packages and Latin Modern fonts.

For Lean, use the pinned ProveIt checkout at
`c1bda76f7f86d2ade505355980826f625e36fff3`, whose Lean and Mathlib versions
are `v4.32.0`. The polynomial prototype also has a standalone Lake file.
The object-language example must run in an environment that provides the
repository's `ConciseIPRA` library.

## Verification status

The LaTeX report was compiled and its rendered pages inspected. Exact
rational and symbolic checks passed. The rational test suite covers 624
small integer quaternion inputs, 31 extra edge cases, 1,965 normalization
checks, three invalid-input rejections, and 21 finite-precision branch tests.
The symbolic checker passes 27 identity groups.

Lean and Lake were unavailable in the authoring environment. Neither Lean
file was compiler-checked, and the complete `Prf PRAAx` geometry derivation
has not been constructed. The source files and completion plan are an
outline/prototype, not a claim of finished formalization. A semantic
Mathlib theorem alone would not prove derivability in iPRA.

The repository was inspected through GitHub at the pinned snapshot; no
repository changes were made.

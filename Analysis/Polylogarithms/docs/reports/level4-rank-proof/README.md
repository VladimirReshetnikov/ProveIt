# Two reflections and exact ranks for level-four double polylogarithms

Research continuation for Vladimir Reshetnikov's **ProveIt** project, prepared
9 October 2026 (America/Los_Angeles). Start with `article.pdf`; `article.tex`
is the complete editable source.

## Main result

This package proves the canonical manuscript conjecture `signed:conj:rank`
at commit `9bc738d3be22b8586a24693f19fb2e2a50ecd1bf`, for exactly the
specified level-four imaginary depth-two product matrix. With its `6w-7`
columns, the ranks are

| Weight | rank A_w | rank A_w with Gaussian columns removed |
| --- | --- | --- |
| odd w >= 3 | 5w-6 | (9w-11)/2 |
| even w >= 2 | 6w-7 | 5w-6 |

The proof gives a complete integer **Q-basis** of the odd-weight nullspace,
not just its dimension. It establishes Gaussian-only saturation by the
same-point shuffle rows and an O(w^2)-arithmetic row-membership test.
Keeping the single-value right sides gives an explicit even-weight compiler.
The article also proves two compact mixed-color leading-index identities in
every even weight and a uniform formal obstruction for the S_(2m) family.

**Scope:** these are ranks of a specified rational matrix, not dimensions of
numerical period spaces. The S4 evaluation remains unproved here. The general
parity principle is known; the article attributes it and does not claim
worldwide priority for individual special-value formulas. The proofs are not
Lean-checked or independently peer reviewed.

## Reproduce

Tested with Python 3.13.5, SymPy 1.14.0, NumPy 2.3.5 and mpmath 1.3.0.
Use a Python version supported by the pinned requirements (Python 3.11 or newer).
From this directory:

```sh
python -m pip install -r requirements.txt
python code/verify.py
python code/numerics.py
make article
```

The exact verifier defaults to `--rank-max 41 --even-max 12`. Do not run it
with Python's `-O` flag: verification assertions must be active. It regenerates
all exact mathematical JSON outputs. Run `python code/test_integration.py`
separately to regenerate the synthetic-fixture integration checks. The separate numerical script regenerates only the
floating-point diagnostic receipt. These commands modify the package's local
data files; they do not modify a repository or contact GitHub.

The mathematical core uses exact integers/rationals and named real symbols.
Modular rank lower bounds at the fixed prime 65521, together with explicit
integer kernel upper bounds, certify the rational ranks. The symbolic
compiler is checked against matrix rows built directly from the two product
laws. No PSLQ or numerical rank estimates are used.

## Package contents

- `article.tex`, `article.pdf`: full article, proofs, context, examples,
  corrections, validation and eight further research directions.
- `code/level4.py`: canonical matrix, nullspace basis, membership certificate,
  exact single-value representation and even-weight compiler.
- `code/verify.py`: exact rank, identity, compatibility and obstruction checks.
- `code/test_integration.py`: synthetic local integration safety checks.
- `code/numerics.py`: independent nested-series diagnostics, expressly not
  outward-rounded interval certificates.
- `data/`: exact rank receipts through weight 41, 210 even-weight identities,
  16 leading-family checks, uniform S-family witnesses, complete weight-five
  matrix and witness, and validation reports.
- `integration/05-level4-rank.tex`: manuscript-ready theorem, proof, compiler
  and identities; compatibility aliases preserve the existing rank labels.
- `integration/apply_integration.py`: opt-in local integration guarded by the
  audited Git blob hash; dry run by default.
- `AUDIT.md`, `RESULTS.md`, `PROVENANCE.json`, `VALIDATION.md`: scope and evidence.
- `MANIFEST.sha256`: hashes for the delivered files, excluding the manifest itself.

See `integration/README.md` before integration. The remote repository has not
been changed. Historical conjectural files are retained as provenance, not
silently rewritten.

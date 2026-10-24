# Eleven-positive adaptive shear: 111 operations, degree 211

[positive11.json](positive11.json) is a complete polynomial circuit in eleven strictly positive integer variables, using the whole fixed compact44 tuple. It has 111 live binary operations and exact degree 211. The [ordinary proof](PROOF.md) composes the polynomial-shears double center with the independently reviewed q²Y main carrier, deleting a single redundant scalar-four gate.

This improves the delivered 112/211 shear point and the 111/269 Pell-congruences point. It is a degree/operation improvement within this positive-domain family, not a global simplest-equation claim. The native compiler/refutation calibration remains inherited; no new Lean/internal certificate is claimed, and formalization is paused.

Run:

```
python3 build.py --check
python3 check.py
python3 -O check.py
```

Only Python's standard library is needed. `build.py` also authenticates the actual four numeral payloads already stored under source44. `check.py` is transparently adapted from the incoming shear auditor; its changes and pinned original are in [SOURCE_PINS.json](SOURCE_PINS.json) and `upstream/`. The complete literal, normal/optimized audit receipts and the 229-term double-center certificate are supplied. Source snapshots and their license are retained without changes. Independent review, when available, is a separate artifact.

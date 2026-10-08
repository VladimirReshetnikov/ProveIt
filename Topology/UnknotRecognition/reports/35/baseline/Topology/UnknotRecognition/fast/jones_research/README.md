# Jones polynomial research checks

`audit_residual_twists.py` audits a consequence of Lemma 5.8 and the universal
geometric realization asserted by Proposition 5.12 of
[Carmi–Cohen, arXiv:2606.22410v1](https://arxiv.org/html/2606.22410v1).
An explicit trefoil seed with a nine-crossing anti-parallel replacement has
Jones–Vassiliev degree 23, exceeding the implied residual degree cap 22.
The script checks full polynomials, formal coordinate conversions, oriented
smoothing reductions, and host anchors. This is a contradiction to the
combined prerequisite claims, not a counterexample to Jones unknot detection
or a localization of the faulty clasp-machine step. `PASS` means the audit's
independent calculations and recorded counterexample agree.

Run from `fast/`:

```sh
python -B jones_research/audit_residual_twists.py --output results/residual_twist_local.json
python -B benchmark_jones_identity_shortcut.py --output results/jones_identity_shortcut_local.json
```

`before_identity_shortcut.py` is the exact production `faithful_jones.py`
from commit `58006240adfeccea75c991249914611d6d96448c`, preserved for paired
timings. It is loaded under the `fastunknot` package so its relative imports
use the unchanged common evaluator. The benchmark records its SHA-256,
checks complete-result equality, and includes a repeated baseline arm.
These full-polynomial timings do not imply faster recognition: recognition
already requests polynomial identity without decoding all coefficients.

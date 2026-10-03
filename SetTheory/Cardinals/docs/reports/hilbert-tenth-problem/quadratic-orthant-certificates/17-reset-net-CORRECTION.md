# Exact-domain API correction, 3 October 2026

## Status and scope

Two malformed-input defects were reproduced in the frozen delivered archive, SHA-256 `b1efbc90aac106061e93ffc92adda686b8e1b9f57539aae976bf227dffec83e3`. This correction changes only the public input boundary in `peak_quadratic.compile_peak`, `build_net.fire`, and the adjacent default `build_net.initial` helper. Invalid values now raise `ValueError` before branching or arithmetic, including under Python optimization.

The valid-natural-domain theorem, nonnegative-real certificate results, duration-parity limitation, all polynomial formulas and arithmetic counts are unchanged. The report PDF and LaTeX, source tables, literal nets, exported schemas, traces, and witness fixtures remain byte-for-byte identical. No optional natural-only gate simplification or other optimization is included. This is not a comprehensive hardening of every internal helper or caller-supplied net/schema structure. Existing author checkers still require assertions enabled; only the new explicit boundary regression is also run with `-O`.

## Exact reproducers in the original package

From the package root:

```python
import json
from pathlib import Path
from source_quadratic import semantic_table
from peak_quadratic import compile_peak
from build_net import fire
net = json.loads(Path('reset_net.json').read_text())
table = semantic_table(json.loads(Path('source/virtual3.json').read_text()))
p = compile_peak(table, 1, all_durations=0.5)
print(p['variables']['count'], p['variables']['padding_index'])
# Original: 2813, 2813. Index 2813 is outside declared indices 0..2812.
finish = next(t for t in net['transitions'] if t['name'] == 'finish')
print(fire(net, {'q:DRAIN': 1, 'ghost': 999}, finish))
# Original: ({'q:DONE': 1}, 0), silently discarding unknown mass.
print(fire(net, {'q:DRAIN': 1.0}, finish))
print(fire(net, {'q:DRAIN': True}, finish))
# Original: both return ({'q:DONE': 1}, 0).
print(fire(net, {'q:DRAIN': 1, 'L': -1}, finish))
# Original: ({'L': -1, 'q:DONE': 1}, 0).
```

The corrected version rejects each call. These malformed markings are outside the theorem's natural-marking domain; they are not legal counterexamples to the loss/debt proof.

## Changed-code ledger

- `peak_quadratic.py`: require exact `bool` for both duration options before branching or converting them to counts
- `build_net.py`: require a dictionary whose keys are known exact string place names and whose values are exact nonnegative Python integers before firing; make the existing default initial-counter contract explicit rather than assertion-only
- `checks/audit_exact_domains.py`: add normal/optimized regressions; valid schemas are checked against full-content hashes generated from the frozen original archive
- `run-checks.sh`: append normal and optimized invocations of this regression
- `checks/PADDING_AND_GENERIC_PEAK_RESULTS.json`: refresh only the hashes of the two corrected source files; no mathematical or numeric result changes
- `checks/EXACT_DOMAIN_RESULTS.json`, this correction note, README notice and `SHA256SUMS`: add evidence/documentation and update integrity metadata

## Regression evidence

Both normal Python and `python3 -O checks/audit_exact_domains.py` reject 64 negative cases (63 invalid-input/option calls and one disabled transition), match nine complete original schemas (h = 1, 2, 3 with all three valid duration modes), replay all 388 stored legal firings unchanged, and check 72 weighted consume/reset/produce overlap cases. The invalid-input checks use explicit conditionals, not assertions.

The full `run-checks.sh` reruns all fourteen original author stages plus the two new boundary stages. Mathematical data bytes are checked separately against the frozen archive. Replay and manifest verification require the Python standard library only.

## Source-review provenance

The narrow independently implemented correction follows inspection of the [pinned upstream review](https://github.com/VladimirReshetnikov/ProveIt/blob/9df1f72ca38dc2def4b70d6e00dfa00edde7f540/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_reset_petri_net_aebfa386e.md) and its adjacent `reset_net_exact_domains.patch`. External code was read, not executed. The original delivered archive remains preserved unchanged.

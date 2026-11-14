"""Recheck whole-instruction failure of the six local-filter survivors."""
from pathlib import Path
import json
import symbolic_core as c

HERE = Path(__file__).resolve().parent
rows, labels = c.machine()
contracts = c.contracts()
result = []
for line in (HERE / 'full_two_row_candidates.txt').read_text().splitlines():
    fields = line.split()
    assert fields[0] == 'rejected'
    drop, keep, w0, d0, n0, w1, d1, n1, *_ = map(int, fields[1:])
    dr, kr = labels[drop], labels[keep]
    changed = {(q, b): (w, d, kr if n == dr else n)
               for (q, b), (w, d, n) in rows.items() if q != dr}
    changed[kr, 0] = (w0, d0 == 1, labels[n0])
    changed[kr, 1] = (w1, d1 == 1, labels[n1])
    check = c.validate(changed, contracts)
    assert not check['ok']
    result.append({'drop': drop, 'keep': keep, 'runtime': check})
expected = json.loads((HERE / 'full_two_row_macro_rejections.json').read_text())
assert json.loads(json.dumps(result)) == expected
print(json.dumps(result, indent=2))

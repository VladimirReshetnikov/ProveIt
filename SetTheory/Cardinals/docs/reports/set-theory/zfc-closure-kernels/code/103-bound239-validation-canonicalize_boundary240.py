"""Canonicalize the repaired reference with the existing verified label map."""
from pathlib import Path
import hashlib
import json
import independent_runtime as r

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'boundary240'
record = json.loads((ROOT / 'baseline/rotation240/renumbering.json').read_text())
mapping = {int(k): v for k, v in record['old_to_new'].items()}
old = r.table(OUT / 'boundary240_old.tm')
if {q for q, _ in old} != set(mapping) - {254}:
    raise ValueError('Different working-label set')
new = {(mapping[q], b): (w, d, mapping[n]) for (q, b), (w, d, n) in old.items()}
if set(new) != {(q, b) for q in range(240) for b in (0, 1)}:
    raise ValueError('Not exactly240 total working states')
literal = '#! start 0\n' + ''.join(f'{q} {b} {w} {"R" if d == 1 else "L"} {n}\n'
                                  for (q, b), (w, d, n) in sorted(new.items()))
path = OUT / 'boundary240.tm'
path.write_text(literal)
again = r.table(path)
for key, val in old.items():
    q, b = key
    w, d, n = val
    if again[mapping[q], b] != (w, d, mapping[n]):
        raise ValueError('Literal row isomorphism failed')
(OUT / 'renumbering.json').write_text(json.dumps(record, indent=2) + '\n')
result = {'status': 'LITERAL_ACTION_ISOMORPHISM_PASS',
          'canonical_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
          'old_sha256': hashlib.sha256((OUT / 'boundary240_old.tm').read_bytes()).hexdigest(),
          'states': 240, 'rows': 480, 'start': 0, 'dispatch': 84, 'halt': 240,
          'scope': 'Exact bijective relabeling including final writes and moves; runtime belongs to the referenced old-label table.'}
(OUT / 'canonicalization.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))

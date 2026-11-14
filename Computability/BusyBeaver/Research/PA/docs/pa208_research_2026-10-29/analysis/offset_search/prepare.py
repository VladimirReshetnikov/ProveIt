import importlib.util
import json
import random
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / 'upstream/U208_ConPA_Entry_Context_2026-10-29/u208_conpa_entry_context_2026-10-29/research/discover_folds.py'
spec = importlib.util.spec_from_file_location('discover', SOURCE)
d = importlib.util.module_from_spec(spec)
spec.loader.exec_module(d)
TABLE = ROOT / 'upstream/U208_ConPA_2026-10-29/U208_ConPA_2026-10-29/machine/u208.native.tm'
t = d.read_table(TABLE)
states = sorted({q for q, b in t})
idx = {q: i for i, q in enumerate(states)}
idx[254] = len(states)
contexts = d.history_contexts(t, 8)
rng = random.Random(20261029)
lines = [str(len(states))]
for q in states:
    rows = [idx[q]]
    for b in (0, 1):
        w, m, z = t[q, b]
        rows.extend((w, m, idx[z]))
    ds = {m for (p, b), (w, m, z) in t.items() if z == q and p != q}
    rows.append(-2 * next(iter(ds)) if len(ds) == 1 and q != 0 else 0)
    lines.append(' '.join(map(str, rows)))
for q in states:
    for b in (0, 1):
        cs = [dict(c) for c in contexts[q] if dict(c).get(0, b) == b]
        chosen = cs if len(cs) <= 6 else rng.sample(cs, 6)
        lines.append(f'{idx[q]} {b} {len(chosen)*2}')
        for c in chosen:
            for repeat in range(2):
                tape = [rng.randrange(2) for _ in range(160)]
                for pos, val in c.items():
                    tape[pos+80] = val
                tape[80] = b
                lines.append(''.join(map(str, tape)))
(Path(__file__).parent/'input.txt').write_text('\n'.join(lines)+'\n')
(Path(__file__).parent/'labels.json').write_text(json.dumps(states+[254]))
print('Prepared', len(states), 'states and', sum(map(len, contexts.values())), 'contexts')

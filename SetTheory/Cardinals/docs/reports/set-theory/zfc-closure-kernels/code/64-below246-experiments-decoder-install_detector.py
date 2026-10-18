#!/usr/bin/env python3
"""Install an independently replayed detector into the exact Context246 table.

This produces an experimental table, not a stand-alone ZFC endpoint proof.
The detector contract and callers' entry invariant must be justified in the
surrounding simulation. Fixed read-1 entry models preserve the existing
register-induction support rows, which the fold checker verifies separately.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
from verify_detector import check_model

ROOT = Path(__file__).resolve().parent
BASE = Path(os.environ.get('ZFC246_BASE', ROOT.parents[1] / 'baseline/context246'))
COUNTER = [6, 9, 13, 19, 29, 41, 58, 74]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('model', type=Path)
    ap.add_argument('--output', type=Path, required=True)
    a = ap.parse_args()
    verified = check_model(a.model)
    record = json.loads(a.model.read_text())
    n = record['states']
    assert 1 <= n <= 8
    source = BASE / 'machine/zfc_prefix246_old.tm'
    table = {}
    for line in source.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, b, w, d, target = line.split()
        table[int(q), int(b)] = (int(w), d, int(target))
    incoming = [(q, b, w, d, t) for (q, b), (w, d, t) in table.items()
                if q not in COUNTER and t in COUNTER]
    assert incoming == [(4, 0, 0, 'L', 6)], incoming
    old_table = dict(table)
    table = {key: row for key, row in table.items() if key[0] not in COUNTER}
    labels = COUNTER[:n] + [4, 84]
    for q, b, w, d, target in record['table']:
        table[labels[q], b] = (w, d, labels[target])
    a.output.write_text('#! start 95\n' + ''.join(
        f'{q} {b} {w} {d} {target}\n'
        for (q, b), (w, d, target) in sorted(table.items())))
    audit = {
        'status': 'local_model_replayed_and_installed',
        'baseline_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
        'model_sha256': verified['model_sha256'],
        'table_sha256': hashlib.sha256(a.output.read_bytes()).hexdigest(),
        'working_states': len(table) // 2,
        'model_labels': labels,
        'external_counter_incoming': incoming,
        'changed_rows': [dict(state=q, read=b, before=old_table[q, b], after=table.get((q, b)))
                         for q, b in sorted(old_table)
                         if table.get((q, b)) != old_table[q, b]],
        'scope': 'Independent nine-contract detector replay plus exact row installation only; surrounding instruction/startup validation is separate.'
    }
    a.output.with_suffix('.json').write_text(json.dumps(audit, indent=2) + '\n')
    print(json.dumps(audit, indent=2))


if __name__ == '__main__':
    main()

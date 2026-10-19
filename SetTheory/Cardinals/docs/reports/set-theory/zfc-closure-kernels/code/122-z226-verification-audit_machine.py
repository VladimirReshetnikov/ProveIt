#!/usr/bin/env python3
"""Independent literal audit of the delivered K226 state renumbering."""
from pathlib import Path
import argparse
import hashlib
import json

OLD_HASH = '0d6740bbc94a92c9696ed92732b1828bec89109f8ebb6859bbb9197e2076ec89'
NEW_HASH = '789e9d1cf04567223823bfdda7d0b4922d7018718fc0daf67c6f5b0c6b4c9b26'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def read(path):
    starts, rows = [], {}
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):
            starts.append(int(line[9:]))
        elif line and not line.startswith('#'):
            q, b, w, d, z = line.split()
            q, b, w, z = int(q), int(b), int(w), int(z)
            require(q >= 0 and z >= 0 and b in (0,1) and w in (0,1)
                    and d in ('L','R') and (q,b) not in rows, 'Malformed row')
            rows[q,b] = w, d, z
    states = {q for q,b in rows}
    halt = {z for w,d,z in rows.values()} - states
    require(starts == [0] and len(halt) == 1, 'Start or halt census')
    require(set(rows) == {(q,b) for q in states for b in (0,1)}, 'Partial table')
    return rows, states, next(iter(halt))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--old-table', type=Path, required=True)
    ap.add_argument('--canonical', type=Path, required=True)
    ap.add_argument('--renumbering', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    require(hashlib.sha256(args.old_table.read_bytes()).hexdigest() == OLD_HASH, 'Old table pin')
    require(hashlib.sha256(args.canonical.read_bytes()).hexdigest() == NEW_HASH, 'Canonical table pin')
    old, old_states, old_halt = read(args.old_table)
    new, new_states, new_halt = read(args.canonical)
    data = json.loads(args.renumbering.read_text())
    mapping = {int(q): int(z) for q,z in data['old_to_new'].items()}
    require(old_states == set(range(230)) - {65,79,140,175}, 'Deleted original K labels')
    require(old_halt == 254 and new_halt == 226, 'Halt labels')
    require(new_states == set(range(226)), 'Canonical working labels')
    require(set(mapping) == old_states | {254} and set(mapping.values()) == set(range(227)),
            'Not a bijection on all working and terminal states')
    require(mapping[0] == 0 and mapping[84] == 82 and mapping[254] == 226,
            'Start, dispatcher or terminal not preserved')
    require(all(new[mapping[q],b] == (w,d,mapping[z])
                for (q,b),(w,d,z) in old.items()), 'Literal transition mismatch')
    require([mapping[q] for q in data['new_to_old']] == list(range(227)), 'Inverse map')
    reached = {0}
    while True:
        more = reached | {z for (q,b),(w,d,z) in new.items() if q in reached}
        if more == reached:
            break
        reached = more
    require(reached == set(range(227)), 'Syntactically unreachable table state')
    result = dict(status='EXACT_LITERAL_BIJECTION_PASS', working_states=226, rows=452,
                  start=0, halt=226, dispatcher=82,
                  deleted_original_K_states=[65,79,140,175],
                  old_sha256=OLD_HASH, canonical_sha256=NEW_HASH,
                  all_states_graph_reachable=True,
                  scope='Every literal row is conjugate by the supplied bijection. '
                        'No transition, tape symbol, head movement or time step changes. '
                        'Graph reachability is syntactic, not a claim about the blank run.')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()

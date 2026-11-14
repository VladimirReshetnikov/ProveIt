#!/usr/bin/env python3
"""Independent, finite whole-tape proof audit of the 213-to-212 bypass.

Every path is executed with a partial tape. Reading an unspecified cell
fails, so successful paths certify the assertion for every exterior tape.
This is an ordinary Python checker, not a proof-assistant kernel.
"""
from pathlib import Path
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
PARENT = ROOT / 'inputs/parent213.native.tm'
CHILD = ROOT / 'machine/u212.native.tm'

def need(test, message):
    if not test:
        raise ValueError(message)

def read(path):
    result = {}
    starts = []
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):
            starts.append(int(line[9:]))
        if not line or line.startswith('#'):
            continue
        q, bit, write, direction, target = line.split()
        key = int(q), int(bit)
        need(key not in result, 'duplicate row')
        need(direction in ('L', 'R'), 'bad direction')
        need(int(bit) in (0, 1) and int(write) in (0, 1), 'nonbinary symbol')
        result[key] = int(write), -1 if direction == 'L' else 1, int(target)
    states = {q for q, bit in result}
    need(starts == [0], 'initial state must be 0')
    need(set(result) == {(q, bit) for q in states for bit in (0, 1)},
         'incomplete transition table')
    need(0 in states and 254 not in states, 'working-state convention')
    need({target for write, direction, target in result.values()} - states == {254},
         'invalid halting target or dangling working-state target')
    return result

def execute(table, state, head, cells, count):
    tape = dict(cells)
    path = []
    for step in range(count):
        need(state != 254, 'interior halt')
        need(head in tape, 'read of an unspecified exterior cell')
        old = tape[head]
        write, direction, target = table[state, old]
        path.append([state, head, old, write, direction, target])
        tape[head] = write
        state = target
        head += direction
    return (state, head, tape), path

def premises(parent, intermediate, child):
    need(len(parent) == 426 and len(child) == 424, 'state census')
    need(set(parent) - set(child) == {(112, 0), (112, 1)}, 'deleted rows')
    need(not set(child)-set(parent), 'added rows')
    need({k for k in child if child[k] != parent[k]} == {(180, 1), (172, 0)}, 'changed rows')
    need(parent[180, 1] == (1, 1, 172), 'old bypass entry')
    need(child[180, 1] == (1, 1, 211), 'new bypass entry')
    need(parent[172, 0] == (0, -1, 112), 'old fold entry')
    need(child[172, 0] == (0, -1, 67), 'new fold entry')
    need(sorted(k for k, v in parent.items() if v[2] == 172) == [(116,0), (180,1)],
         'all old entries to 172')
    need(sorted(k for k, v in intermediate.items() if v[2] == 172) == [(116,0)],
         'all intermediate entries to 172')
    need(intermediate[116,0] == (0,1,172), 'preceding-zero producer')
    need(sorted(k for k,v in intermediate.items() if v[2] == 112) == [(172,0)],
         'all entries to removed state')
    need(all(v[2] != 112 for v in child.values()), 'dangling target')
    need(0 not in (112, 172), 'initial state exceptional')

def blocks(parent, intermediate, child):
    specifications = [
        ('bypass_11', parent, intermediate, 180, {0:1, 1:1}, 2, 2, (184,2)),
        ('bypass_100', parent, intermediate, 180, {0:1, 1:0, 2:0}, 7, 3, (90,3)),
        ('bypass_101', parent, intermediate, 180, {0:1, 1:0, 2:1}, 7, 3, (86,3)),
        ('fold_00', intermediate, child, 172, {-1:0, 0:0}, 4, 2, (151,0)),
    ]
    records = []
    for name, old, new, start, cells, old_n, new_n, endpoint in specifications:
        a, path_a = execute(old, start, 0, cells, old_n)
        b, path_b = execute(new, start, 0, cells, new_n)
        need(a == b, name+': unequal complete local result')
        need(a[:2] == endpoint, name+': unexpected endpoint')
        need(a[2] == cells, name+': tape modified')
        records.append(dict(name=name, local_cells=cells, old_steps=old_n,
                            new_steps=new_n, old_path=path_a, new_path=path_b,
                            endpoint=endpoint, exterior_unread=True,
                            entire_tape_unchanged=True))
    return records

def blank_prefix(table, count=48140):
    state, head, ones = 0, 0, set()
    modified_visits = {str(key): 0 for key in ((180,1), (172,0), (112,0), (112,1))}
    dispatcher_visits = 0
    for _ in range(count):
        need(state != 254, 'unexpected blank-prefix halt')
        dispatcher_visits += state == 84
        key = state, int(head in ones)
        if str(key) in modified_visits:
            modified_visits[str(key)] += 1
        write, direction, state = table[key]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += direction
    return dict(steps=count, state=state, head=head, ones=sorted(ones),
                modified_row_visits=modified_visits,
                earlier_dispatcher_visits=dispatcher_visits)

def run(parent_path=PARENT, child_path=CHILD):
    """Return the complete receipt without writing files."""
    parent_path, child_path = Path(parent_path), Path(child_path)
    parent, child = read(parent_path), read(child_path)
    intermediate = dict(parent)
    intermediate[180,1] = (1,1,211)
    premises(parent, intermediate, child)
    records = blocks(parent, intermediate, child)
    startup = blank_prefix(parent)
    need(blank_prefix(child) == startup, 'blank prefix differs')
    need(startup['state'] == 84 and startup['head'] == -2
         and len(startup['ones']) == 120, 'wrong calibrated prefix frame')
    need(not any(startup['modified_row_visits'].values()), 'edited row in blank prefix')
    failures = []
    for name, stage, row, action in [
        ('wrong_bypass_target', 'intermediate', (180,1), (1,1,167)),
        ('wrong_bypass_write', 'intermediate', (180,1), (0,1,211)),
        ('wrong_fold_target', 'child', (172,0), (0,-1,68)),
        ('wrong_fold_direction', 'child', (172,0), (0,1,67)),
        ('wrong_fold_write', 'child', (172,0), (1,-1,67)),
        ('broken_helper', 'child', (67,0), (1,1,151)),
    ]:
        mid, end = dict(intermediate), dict(child)
        (mid if stage == 'intermediate' else end)[row] = action
        rejected = False
        try:
            blocks(parent, mid, end)
        except (ValueError, KeyError):
            rejected = True
        need(rejected, 'mutation was not rejected: '+name)
        failures.append(name)
    output = dict(
        status='PASS', parent_sha256=hashlib.sha256(parent_path.read_bytes()).hexdigest(),
        child_sha256=hashlib.sha256(child_path.read_bytes()).hexdigest(),
        literal_row_delta_checked=True, complete_incoming_inventories_checked=True,
        exact_paths=records, blank_prefix=startup,
        semantic_negative_controls_rejected=failures,
        scope='Universal finite path identities over arbitrary opaque tape exterior; ordinary Python, not a PA certificate.',
    )
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--parent', type=Path, default=PARENT)
    parser.add_argument('--candidate', type=Path, default=CHILD)
    parser.add_argument('--output', type=Path,
                        help='Write the full receipt to this explicit path.')
    args = parser.parse_args()
    receipt = run(args.parent, args.candidate)
    if args.output is not None:
        args.output.write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps({
        'status': receipt['status'],
        'parent_sha256': receipt['parent_sha256'],
        'child_sha256': receipt['child_sha256'],
        'universal_path_identities': len(receipt['exact_paths']),
        'semantic_negative_controls_rejected': len(
            receipt['semantic_negative_controls_rejected']),
        'identical_blank_prefix_steps': receipt['blank_prefix']['steps'],
        'complete_incoming_inventories_checked': True,
    }, sort_keys=True))


if __name__ == '__main__':
    main()

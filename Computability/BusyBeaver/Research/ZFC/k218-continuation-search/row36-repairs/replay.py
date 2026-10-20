"""Replay the six finite counterexample traces; no submitted imports or search."""
from pathlib import Path
import argparse
import gzip
import hashlib
import json

p = argparse.ArgumentParser()
p.add_argument('--repo', type=Path, required=True)
p.add_argument('--evidence', type=Path, default=Path(__file__).resolve().parent)
p.add_argument('--output', type=Path, required=True)
a = p.parse_args()
assert not a.output.exists(), 'fresh output required'
base = a.repo / 'Computability/BusyBeaver/Research/ZFC/candidate-k218'
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
record = json.loads((a.evidence / 'result.json').read_text())
table = {}
for line in (base / 'k218.native.tm').read_text().splitlines():
    if not line.strip() or line.startswith('#'):
        continue
    state, read, write, direction, target = line.split()
    table[int(state), int(read)] = int(write), direction, int(target)
assert sha(base / 'k218.native.tm') == '2dfaba6da09b78291e534777cd30c5f0d68bd84faa670e868e779c396aeb308f'
sites = json.loads((base / 'sites218.json').read_text())
boot = json.loads((base / 'evidence/blank-startup.json').read_text())
phy = [6, 2, 0, 4, 3, 7, 8, 5, 1]

def encode_frame(frame):
    """Construct the entire support, independently of check.py's frame decoder."""
    head, header = frame['head'], frame['header']
    assert header - head == 64 + frame['gap']
    support = {head - 1, header}
    path = sites[frame['ordinal']][0]
    support.update(head + i for i, bit in enumerate(path) if bit == '1')
    physical = [None] * 9
    for logical, slot in enumerate(phy):
        physical[slot] = frame['registers'][logical]
    cursor = header + 1
    for value in physical + frame['spares']:
        assert isinstance(value, int) and value >= 0
        cursor += 1  # leading zero
        support.update(range(cursor, cursor + value + 1))
        cursor += value + 1
    return support

receipts = []
for name, end in record['records'].items():
    current_table = dict(table)
    if name != 'accepted218':
        current_table = {k: v for k, v in current_table.items() if k[0] != 301}
        current_table.update({(87, 0): (0, 'R', 88), (88, 0): (0, 'L', 51),
                              (51, 0): (0, 'R', 122)})
    if 'boot36to' in name:
        target = 10 if 'boot36to10' in name else 6
        current_table[36, 0] = 1, 'L', target
    if name.endswith('_following'):
        parent = record['records'][name.removesuffix('_following')]
        state, head, support = 84, parent['head'], set(parent['end_one_cells'])
    else:
        state, head, support = 84, -5, set(boot['final_one_cells'])
    trace_path = a.evidence / end['trace_file']
    trace = json.loads(gzip.decompress(trace_path.read_bytes()))
    assert len(trace) == end['steps'] <= 10000
    hits = []
    for tick, row in enumerate(trace):
        read = int(head in support)
        write, direction, target = current_table[state, read]
        displacement = {'L': -1, 'R': 1}[direction]
        assert row == [state, head, read, write, displacement, target]
        if (state, read) == (36, 0):
            hits.append({'tick': tick, 'head': head,
                         'nearby_ones': sorted(x for x in support if abs(x - head) <= 10)})
        support.discard(head)
        if write:
            support.add(head)
        state, head = target, head + displacement
        assert state != 254
    assert hits == end['row36_0_uses']
    assert (state, head) == (end['end_state'], end['head'])
    assert support == set(end['end_one_cells']) == encode_frame(end)
    receipts.append({'trace': name, 'steps': len(trace), 'ordinal': end['ordinal'],
                     'registers': end['registers'], 'trace_sha256': sha(trace_path)})

# Check the finite source trace using subtree intervals rather than binary increment.
source_trace = json.loads((a.evidence / 'source-fragment.json').read_text())
def unwind(path, edge, count):
    while path:
        last, path = path[-1], path[:-1]
        if last == edge:
            count -= 1
            if count == 0:
                indices = [i for i, row in enumerate(sites) if row[0].startswith(path)]
                return (max(indices) + 1) % len(sites) if edge == '0' else min(indices)
    return 0

ordinal, values = 0, [3, 0, 0, 0, 3, 0, 0, 0, 0]
for row in source_trace['trace']:
    path, op, arg = sites[ordinal]
    assert row['ordinal'] == ordinal and row['instruction'] == sites[ordinal]
    assert row['before'] == values
    target = ordinal + 1
    if op == 'CI':
        values[arg] += 1
    elif op == 'CD':
        if values[arg] == 0:
            target = unwind(path, '0', 1)
        else:
            values[arg] -= 1
    elif op in ('CB', 'CC'):
        target = unwind(path, '0' if op == 'CB' else '1', arg)
    else:
        raise AssertionError(op)
    assert (row['next'], row['after']) == (target, values)
    ordinal = target
assert ordinal == 9 and values == [4, 0, 0, 0, 3, 0, 0, 0, 3]
assert len(source_trace['trace']) == 25
out = {'status': 'FINITE_TRACE_AND_FULL_SUPPORT_REPLAY_PASS',
       'scope': 'Finite reachable contract counterexamples only; no whole-run theorem.',
       'binary_transitions': sum(r['steps'] for r in receipts), 'traces': receipts,
       'source_steps': 25, 'source_final_ordinal': ordinal, 'source_final_registers': values,
       'replay_sha256': sha(Path(__file__)), 'record_sha256': sha(a.evidence / 'result.json'),
       'source_trace_sha256': sha(a.evidence / 'source-fragment.json')}
a.output.write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps({k: v for k, v in out.items() if k != 'traces'}))

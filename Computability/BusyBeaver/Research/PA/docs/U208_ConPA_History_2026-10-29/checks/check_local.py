#!/usr/bin/env python3
"""Rebuild U208 and prove the new U209-to-U208 finite macro simulation.

No compiler, proof-search code, source optimizer, history-search result, or
symbolic arithmetic engine is imported. All checks remain active under -O.
"""
from pathlib import Path
import argparse, hashlib, json

ROOT = Path(__file__).resolve().parents[1]
PARENT_SHA = '891455876f2684b2bd2a9118092715590028fbdb227aa7055030536714d8b7a4'
NATIVE_SHA = '36b58fea7a184b1050914170e8f5240c8a13da218dbbfa7e1985cd73d516e5c7'
DENSE_SHA = '926d15c43daebdafd099723f265b073c25bf21a15e4c5593e669ccac6f70f8d0'

def require(ok, message):
    if not ok:
        raise ValueError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def encode(table):
    lines = ['#! start 0\n']
    for (state, bit), (write, direction, target) in sorted(table.items()):
        move = 'R' if direction == 1 else 'L'
        lines.append(f'{state} {bit} {write} {move} {target}\n')
    return ''.join(lines).encode()

def census(table, count, halt):
    states = {q for q, _ in table}
    require(len(states) == count, 'Working-state count')
    require(0 in states and halt not in states, 'Initial/halt state')
    require(set(table) == {(q, b) for q in states for b in (0, 1)}, 'Totality')
    require({z for w, d, z in table.values()} - states == {halt}, 'Closure')
    require(all(w in (0, 1) and d in (-1, 1) for w, d, z in table.values()),
            'Binary alphabet and moving-head convention')
    reached = {0}
    pending = [0]
    while pending:
        q = pending.pop()
        for b in (0, 1):
            z = table[q, b][2]
            if z != halt and z not in reached:
                reached.add(z)
                pending.append(z)
    require(reached == states, 'Graph reachability')
    return states

def read(path, count, halt=254):
    table = {}
    starts = []
    for line in Path(path).read_text().splitlines():
        if line.startswith('#! start '):
            starts.append(int(line[9:]))
        if not line or line.startswith('#'):
            continue
        q, b, w, d, z = line.split()
        q, b, w, z = map(int, (q, b, w, z))
        require(d in ('L', 'R') and (q, b) not in table, 'Malformed row')
        table[q, b] = (w, 1 if d == 'R' else -1, z)
    require(starts == [0], 'Start marker')
    census(table, count, halt)
    return table

def incoming(table, target):
    return sorted([q, b, w, d] for (q, b), (w, d, z) in table.items()
                  if z == target)

def execute(table, state, cells, steps):
    tape, head, trace = dict(cells), 0, []
    for _ in range(steps):
        require(state != 254, 'Unexpected intermediate halt')
        require(head in tape, 'Opaque exterior read')
        bit = tape[head]
        write, direction, target = table[state, bit]
        trace.append([state, head, bit, write, direction, target])
        tape[head] = write
        head += direction
        state = target
    return (state, head, tape), trace

def certify(old, new):
    census(old, 209, 254)
    census(new, 208, 254)
    rho = lambda q: 172 if q == 211 else q
    require(set(old) - set(new) == {(211, 0), (211, 1)} and
            not set(new) - set(old), 'Deleted-state identity')
    inventories = {
        172: [[116, 0, 0, 1]],
        116: [[216, 1, 1, 1]],
        211: [[163, 0, 0, -1], [163, 1, 1, 1]],
        163: [[132, 1, 1, 1], [199, 1, 1, 1], [214, 0, 0, 1]],
        214: [[204, 1, 1, 1]],
    }
    for state, expected in inventories.items():
        require(incoming(old, state) == expected,
                'Entry-invariant inventory for ' + str(state))
    require(not {0} & ({172, 116, 211, 163, 214}),
            'Entry guard cannot be assumed at time zero')
    # These complete inventories establish, on every run from state 0:
    #   old state 172: tape[head-2]=1 and tape[head-1]=0;
    #   old state 211 reading 0: tape[head-1]=1.
    # For the second assertion, a left entrance is 163/0. Entrances
    # 132/1 and 199/1 to 163 put 1 in the eventual scanned cell, hence
    # cannot give 211 reading 0. The remaining path is 204/1,214/0,163/0.
    ordinary = 0
    for (q, b), (w, d, z) in old.items():
        if q not in (172, 211):
            require(new[rho(q), b] == (w, d, rho(z)),
                    'Ordinary quotient row ' + str((q, b)))
            ordinary += 1
    cases = []
    specifications = [
        (172, 0, {-2: 1, -1: 0, 0: 0}, 7),
        (211, 0, {-1: 1, 0: 0}, 3),
        (172, 1, {0: 1}, 1),
        (211, 1, {0: 1}, 1),
    ]
    for q, b, cells, steps in specifications:
        old_end, old_trace = execute(old, q, cells, 1)
        new_end, new_trace = execute(new, rho(q), cells, steps)
        expected = (rho(old_end[0]), old_end[1], old_end[2])
        require(new_end == expected, 'Macro endpoint ' + str((q, b)))
        require(old_end[2] == cells, 'Source macro altered tape')
        require(steps > 0, 'Nonpositive simulation block')
        cases.append({'old_state': q, 'new_state': rho(q), 'scanned': b,
                      'entry_window': cells, 'old_steps': 1,
                      'new_steps': steps, 'old_trace': old_trace,
                      'new_trace': new_trace, 'exterior_unread': True})
    require(ordinary == 414, 'Ordinary-row census')
    return {'status': 'ALL_TAPE_LOCAL_SIMULATION_PASS',
            'old_states': 209, 'new_states': 208,
            'ordinary_rows': ordinary, 'incoming_inventories': inventories,
            'guard_depth': 3, 'cases': cases,
            'minimum_block_steps': 1, 'maximum_block_steps': 7,
            'scope': 'Equivalent halting from state 0 on every common initial tape; '
                     'all exterior cells arbitrary and unread in each special macro.'}

def build(parent):
    new = {(q, b): (w, d, 172 if z == 211 else z)
           for (q, b), (w, d, z) in parent.items() if q != 211}
    new[172, 0] = (0, -1, 214)
    return new

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=ROOT / 'build/local.json')
    args = parser.parse_args()
    parent_bytes = (ROOT / 'inputs/u209.native.tm').read_bytes()
    require(digest(parent_bytes) == PARENT_SHA, 'Frozen parent hash')
    old = read(ROOT / 'inputs/u209.native.tm', 209)
    new = build(old)
    raw = encode(new)
    require(digest(raw) == NATIVE_SHA, 'Native reconstruction hash')
    require(raw == (ROOT / 'machine/u208.native.tm').read_bytes(), 'Native artifact mismatch')
    states = sorted(census(new, 208, 254))
    mapping = {q: i for i, q in enumerate(states)}
    mapping[254] = 208
    dense = {(mapping[q], b): (w, d, mapping[z])
             for (q, b), (w, d, z) in new.items()}
    require(digest(encode(dense)) == DENSE_SHA, 'Dense reconstruction hash')
    require(encode(dense) == (ROOT / 'machine/u208.tm').read_bytes(), 'Dense artifact mismatch')
    census(dense, 208, 208)
    result = certify(old, new)
    mutations = [
        ('172_left_guard', 'old', (116, 0), (1, 1, 172)),
        ('172_second_left_guard', 'old', (216, 1), (0, 1, 116)),
        ('211_direct_left_guard', 'old', (163, 1), (0, 1, 211)),
        ('211_excluded_zero_case', 'old', (132, 1), (0, 1, 163)),
        ('211_excluded_zero_case_2', 'old', (199, 1), (0, 1, 163)),
        ('211_nested_left_guard', 'old', (204, 1), (0, 1, 214)),
        ('wrong_fold_helper', 'new', (172, 0), (0, -1, 204)),
        ('wrong_fold_direction', 'new', (172, 0), (0, 1, 214)),
        ('wrong_recursive_dispatch', 'new', (163, 0), (0, -1, 67)),
        ('wrong_shared_one_branch', 'new', (172, 1), (0, 1, 184)),
        ('wrong_ordinary_row', 'new', (0, 0), (1, 1, 66)),
    ]
    rejected = []
    for label, side, key, action in mutations:
        a, b = dict(old), dict(new)
        (a if side == 'old' else b)[key] = action
        try:
            certify(a, b)
        except (ValueError, KeyError):
            rejected.append(label)
        else:
            raise ValueError('Negative control accepted: ' + label)
    result['negative_controls_rejected'] = rejected
    result['sha256'] = {'parent_native': digest(parent_bytes),
                        'candidate_native': digest(raw),
                        'candidate_dense': digest(encode(dense))}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'cases'}, indent=2))

if __name__ == '__main__':
    main()

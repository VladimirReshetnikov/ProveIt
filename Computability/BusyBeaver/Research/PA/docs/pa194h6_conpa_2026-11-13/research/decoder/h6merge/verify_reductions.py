#!/usr/bin/env python3
"""Reproduce the bounded negative searches; Python 3.10+, standard library.

These checks do not establish a lower bound on consistency-machine size.
The imported symbolic executor retains its original attribution and its
arithmetic-block assumptions. Candidates alter no protected block row.
"""
from pathlib import Path
from collections import defaultdict
import argparse
import hashlib
import itertools
import json
import time

import symbolic_runtime as c

HERE = Path(__file__).resolve().parent


def load(name):
    path = HERE / 'inputs' / name
    rows = {}
    data = (path / 'machine.native.tm').read_bytes()
    for line in data.decode().splitlines():
        q, b, w, d, n = line.split()
        rows[int(q), int(b)] = int(w), d == 'R', int(n)
    sites = json.loads((path / 'sites.json').read_text())
    instructions = json.loads((path / 'instructions.json').read_text())
    contracts = []
    frame = lambda i, extra=0, effect=c.PLAIN: c.frame(
        tuple(map(int, sites[i][0])), extra, effect)
    for i, ins in enumerate(instructions):
        start = frame(i)
        if ins[0] == 'inc':
            _, r, nxt = ins
            contracts.append((i, None, start, c.canonical(
                frame(nxt, 0, ('x', 'inc', c.PHYSICAL[r])))))
        elif ins[0] == 'dec':
            _, r, zero, positive = ins
            contracts.append((i, (c.PHYSICAL[r], True), start,
                              c.canonical(frame(zero))))
            contracts.append((i, (c.PHYSICAL[r], False), start, c.canonical(
                frame(positive, 1, ('x', 'dec', c.PHYSICAL[r])))))
        elif ins[0] == 'jump':
            contracts.append((i, None, start, c.canonical(frame(ins[1]))))
        else:
            assert ins == ['halt']
            contracts.append((i, None, start, None))
    return rows, sites, instructions, contracts, hashlib.sha256(data).hexdigest()


def startup(rows, name):
    expected = json.loads((HERE / 'inputs' / name / 'startup.json').read_text())
    tape, q, head = set(), 74, 0
    observed = set(c.BOXSTATES)
    for _ in range(expected['steps']):
        observed.add(q)
        w, d, q = rows[q, int(head in tape)]
        (tape.add if w else tape.discard)(head)
        head += 1 if d else -1
        assert q != 254
    assert (q, head, tape) == (expected['state'], expected['head'],
                                set(expected['one_cells']))
    return observed


def scanner_alignment_witness(rows, shortened):
    # Source site 0, affine gap parameter 0, ten zero-valued physical registers.
    # The finite frame is 1 000000 0^42 1 (01)^10.
    initial = {-1, 48} | set(range(50, 69, 2))
    target = initial | {4}
    result = {}
    for name, table, limit in [('parent', rows, 486), ('shortened', shortened, 236)]:
        q, head, tape, returns = 84, 0, set(initial), []
        for step in range(1, limit + 1):
            w, d, q = table[q, int(head in tape)]
            (tape.add if w else tape.discard)(head)
            head += 1 if d else -1
            if q == 84:
                returns.append([step, head])
        if name == 'parent':
            assert (q, head, tape) == (84, 0, target)
            assert returns == [[116, 0], [246, 0], [486, 0]]
        else:
            assert (q, head) == (84, 8)
            assert returns == [[100, 0], [236, 8]]
        result[name] = {'first_returns_to_control_84': returns,
                        'final_head': head, 'final_state': q}
    return result


def quick_checks():
    out = {}
    for name, expected_count in [('primary', 4780), ('PA194HS', 4750)]:
        rows, sites, ins, contracts, digest = load(name)
        observed = startup(rows, name)
        result = c.validate(rows, contracts, observe=lambda s: observed.add(s[0]))
        assert result['ok'] and result['contracts'] == expected_count
        unseen = sorted({q for q, _ in rows} - observed)
        assert not unseen
        out[name] = {'native_sha256': digest, 'baseline': result,
                     'unseen_controls_after_source_and_startup': unseen}
        if name != 'PA194HS':
            continue
        shortened = {key: (w, d, 75 if n == 34 else n)
                     for key, (w, d, n) in rows.items() if key[0] != 34}
        failures = []
        for index, contract in enumerate(contracts):
            if c.run(shortened, contract, fuel=1024) is None:
                failures.append({'index': index, 'site': contract[0],
                                 'branch': contract[1],
                                 'source': sites[contract[0]],
                                 'instruction': ins[contract[0]]})
        frozen = json.loads((HERE / 'evidence' /
                             'PA194HS_short_scan_failed.json').read_text())
        assert json.loads(json.dumps(failures)) == frozen
        assert len(failures) == 113
        out[name]['six_zero_scanner_failed_contracts'] = len(failures)
        out[name]['symbolic_fuel_bound'] = 1024
        out[name]['finite_scanner_alignment_witness'] = scanner_alignment_witness(
            rows, shortened)
    return out


def whole_contract_merges(name):
    rows, sites, ins, contracts, digest = load(name)
    visits, tests = defaultdict(set), defaultdict(list)
    for index, contract in enumerate(contracts):
        local = set()
        assert c.run(rows, contract, observe=lambda s: local.add(
            (s[0], c.headbit(s[2] if s[1] else s[3])))) is not None
        for q, bit in local:
            visits[q].add(index)
            tests[q, bit].append(index)
    controls = sorted({q for q, _ in rows})
    removable = [q for q in controls if q not in c.BOXSTATES]
    trials, survivors = 0, []
    started = time.monotonic()
    for a in removable:
        for b in controls:
            if a == b or (a > b and b not in c.BOXSTATES):
                continue
            choices = ([(1, 1)] if b in c.BOXSTATES else
                       list(itertools.product((0, 1), repeat=2)))
            for choice in choices:
                patch = {bit: rows[a if choice[bit] == 0 else b, bit]
                         for bit in (0, 1)}
                affected = visits[a] | visits[b]
                order = []
                for q in (a, b):
                    for bit in (0, 1, None):
                        indices = tests.get((q, bit), [])
                        if indices:
                            order += [indices[0], indices[-1],
                                      indices[len(indices) // 2]]
                order = list(dict.fromkeys(order)) + sorted(affected - set(order))
                changed = {}
                for (q, bit), (w, d, nxt) in rows.items():
                    if q == a:
                        continue
                    if q == b:
                        w, d, nxt = patch[bit]
                    changed[q, bit] = w, d, b if nxt == a else nxt
                trials += 1
                for index in order:
                    try:
                        closed = c.run(changed, contracts[index], fuel=1024)
                    except KeyError:
                        closed = None
                    if closed is None:
                        break
                else:
                    result = c.validate(changed, contracts)
                    if result['ok']:
                        survivors.append({'remove': a, 'keep': b,
                                          'rows': choice, 'validation': result})
    assert trials == 62073
    assert not survivors
    return {'input': name, 'native_sha256': digest, 'trials': trials,
            'survivors': survivors, 'symbolic_fuel_bound': 1024,
            'seconds': time.monotonic() - started}


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without Python -O; assertions check the evidence.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--search-merges', action='store_true',
                        help='Repeat both 62,073-candidate searches (about one minute).')
    args = parser.parse_args()
    result = quick_checks()
    if args.search_merges:
        result['merge_searches'] = [whole_contract_merges(name)
                                   for name in ('primary', 'PA194HS')]
    print(json.dumps(result, indent=2))

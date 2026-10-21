#!/usr/bin/env python3
"""Replay the exact startup and local scanner obstruction for delete50.

This proves a finite startup and refutes a proposed scanner stopping lemma.
It does not prove or disprove a separate Con(ZFC) calibration of delete50.
"""
from pathlib import Path
import argparse
import hashlib
import json

PHY = (6, 2, 0, 4, 3, 7, 8, 5, 1)


def table(path):
    result = {}
    for line in path.read_text().splitlines():
        if line and not line.startswith('#'):
            q, b, w, d, z = line.split()
            result[int(q), int(b)] = (int(w), 1 if d == 'R' else -1, int(z))
    return result


def step(t, state, head, ones):
    w, d, q = t[state, int(head in ones)]
    if w:
        ones.add(head)
    else:
        ones.discard(head)
    return q, head + d


def frame(pc, registers, spares, gap=0, head=0):
    physical = [0] * 9
    for j, position in enumerate(PHY):
        physical[position] = registers[j]
    header = head + 64 + gap
    ones = {head - 1, header}
    ones.update(head + j for j, b in enumerate(pc) if b == '1')
    position = header + 1
    for value in physical + spares:
        position += 1
        ones.update(range(position, position + value + 1))
        position += value + 1
    return ones


def decode(head, ones):
    if not ones or min(ones) != head - 1:
        return None
    right = [x for x in ones if x >= head + 52]
    if not right or min(right) < head + 64:
        return None
    header, last = min(right), max(ones)
    position, values = header + 1, []
    while position < last:
        if position in ones or position + 1 not in ones:
            return None
        start = position + 1
        position = start
        while position in ones:
            position += 1
        values.append(position - start - 1)
    if position != last + 1 or len(values) < 10:
        return None
    return {'head': head, 'gap': header - head - 64,
            'pc_ones': sorted(x - head for x in ones if head <= x < header),
            'registers': [values[p] for p in PHY], 'spares': values[9:]}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--accepted', required=True, type=Path)
    p.add_argument('--short', required=True, type=Path)
    p.add_argument('--sites', required=True, type=Path)
    p.add_argument('--output', required=True, type=Path)
    a = p.parse_args()
    old, new = table(a.accepted), table(a.short)
    expected = dict(old)
    del expected[50, 0]
    del expected[50, 1]
    expected[34, 0] = (0, -1, 75)
    assert new == expected
    assert len({q for q, b in new}) == 217 and len(new) == 434

    q, h, ones = 0, 0, set()
    first_root = None
    for tick in range(104083):
        assert q != 254
        if q == 84:
            f = decode(h, ones)
            if f is not None and not f['pc_ones'] and first_root is None:
                first_root = dict(f, steps=tick, support=sorted(ones))
        if tick < 104082:
            q, h = step(new, q, h, ones)
    assert first_root is not None and first_root['steps'] == 104082
    assert q == 84 and h == -6
    assert first_root['registers'] == [4, 3, 0, 0, 3, 0, 0, 0, 0]
    assert first_root['gap'] == 6 and first_root['spares'] == [1] * 59
    assert ones == frame('', first_root['registers'], [1] * 59, 6, -6)

    sites = json.loads(a.sites.read_text())
    pc, op, register = sites[40]
    assert (pc, op, register) == ('1101001001000000', 'CD', 1)
    initial = frame(pc, [0] * 9, [0])
    oq, oh, oo = 84, 0, set(initial)
    for tick in range(288):
        oq, oh = step(old, oq, oh, oo)
    assert (oq, oh) == (34, 10)
    assert 9 in oo and 17 in oo and all(x not in oo for x in range(10, 17))
    nq, nh, no = 84, 0, set(initial)
    for short_tick in range(2000):
        if (nq, nh, no) == (oq, oh, oo):
            break
        nq, nh = step(new, nq, nh, no)
    else:
        raise AssertionError('short table does not reach the scanner checkpoint')
    checkpoint = {'accepted_steps': 288, 'short_steps': short_tick,
                  'state': oq, 'head': oh, 'support': sorted(oo)}
    for _ in range(2):
        oq, oh = step(old, oq, oh, oo)
        nq, nh = step(new, nq, nh, no)
    assert (oq, oh) == (2, 8) and (nq, nh) == (84, 10)
    assert oo == no
    # The accepted primitive has an exact endpoint, checked without a symbolic engine.
    q, h, ones = 84, 0, set(initial)
    for _ in range(588):
        q, h = step(old, q, h, ones)
    prefix = pc[:pc.rfind('0')]
    successor = format(int(prefix, 2) + 1, '0' + str(len(prefix)) + 'b')
    assert (q, h) == (84, 0) and ones == frame(successor, [0] * 9, [0])

    # A direct ordinal CFG for the unchanged source, independent of its compiler.
    index = {p: i for i, (p, _, _) in enumerate(sites)}
    leaves = {}
    def interval(path):
        if path in index:
            result = (index[path], index[path] + 1)
        else:
            left, right = interval(path + '0'), interval(path + '1')
            assert left[1] == right[0]
            result = left[0], right[1]
        leaves[path] = result
        return result
    assert interval('') == (0, len(sites))
    def jump(path, bit, count):
        while path:
            tail, path = path[-1], path[:-1]
            if tail == bit:
                count -= 1
                if count == 0:
                    return leaves[path][1] % len(sites) if bit == '0' else leaves[path][0]
        return 0
    r, position = [4, 3, 0, 0, 3, 0, 0, 0, 0], 0
    for tick in range(2411):
        if tick == 2410:
            assert position == 40 and r == [7, 0, 6, 0, 4, 0, 0, 0, 0]
            break
        path, op, j = sites[position]
        if op == 'CI':
            r[j] += 1
            position = (position + 1) % len(sites)
        elif op == 'CD':
            if r[j]:
                r[j] -= 1
                position = (position + 1) % len(sites)
            else:
                position = jump(path, '0', 1)
        elif op == 'CB':
            position = jump(path, '0', j)
        elif op == 'CC':
            position = jump(path, '1', j)
        else:
            raise AssertionError('unexpected abstract halt')

    receipt = {
        'status': 'STARTUP_AND_LOCAL_SCANNER_OBSTRUCTION_REPLAYED',
        'table_sha256': hashlib.sha256(a.short.read_bytes()).hexdigest(),
        'startup': first_root, 'site': sites[40], 'input_support': sorted(initial),
        'scanner_checkpoint': checkpoint,
        'accepted_after_two_more_steps': {'state': oq, 'head': oh},
        'short_after_two_more_steps': {'state': nq, 'head': nh},
        'accepted_primitive_endpoint_steps': 588,
        'abstract_source_reachability': {'steps': 2410, 'ordinal': 40, 'registers': r},
        'scope': 'Exact finite startup; exact seven-zero wrong-turn witness; '
                 'the affected zero guard is reachable in the intended abstract program. '
                 'No claim of a Con(ZFC) equivalence or inequivalence for the short machine.'
    }
    a.output.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: v for k, v in receipt.items() if k not in
                      ('startup', 'input_support', 'scanner_checkpoint')}, indent=2))


if __name__ == '__main__':
    main()

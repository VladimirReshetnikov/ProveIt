#!/usr/bin/env python3
"""Exact finite source execution, with decoded program counter successors."""
import argparse
import hashlib
import json
from pathlib import Path


def increment(bits):
    j = bits.rfind('0')
    return bits[:j] + '1' + '0' * (len(bits) - j - 1) if j >= 0 else '0' * len(bits)


def strip(bits, char, count):
    for _ in range(count):
        j = bits.rfind(char)
        bits = bits[:j] if j >= 0 else ''
    return bits


def successors(path, op, arg):
    if op == 'CH':
        return []
    if op == 'CI':
        return [increment(path)]
    if op == 'CD':
        return [increment(strip(path, '0', 1)), increment(path)]
    if op == 'CB':
        return [increment(strip(path, '0', arg))]
    if op == 'CC':
        return [strip(path, '1', arg)]
    raise ValueError(op)


def build(sites):
    index = {s[0]: i for i, s in enumerate(sites)}
    maxdepth = max(map(len, index))
    assert len(index) == len(sites)

    def lookup(bits):
        padded = bits + '0' * maxdepth
        for length in range(1, maxdepth + 1):
            if padded[:length] in index:
                assert '1' not in bits[length:]
                return index[padded[:length]]
        raise ValueError(bits)

    edges = [[lookup(bits) for bits in successors(*s)] for s in sites]
    return lookup(''), edges


def execute(sites, initial, targets, limit):
    current, edges = build(sites)
    regs = initial[:]
    digest = hashlib.sha256()
    visits = set()
    for tick in range(limit + 1):
        path, op, reg = sites[current]
        visits.add(current)
        positive = op == 'CD' and regs[reg] > 0
        if (current, positive) in targets:
            return dict(status='REACHED', source_steps=tick, site_index=current,
                        site=sites[current], registers=regs, positive=positive,
                        initial=initial, distinct_sites=len(visits),
                        trace_sha256=digest.hexdigest())
        if tick == limit:
            return dict(status='LIMIT', limit=limit, site_index=current,
                        registers=regs, initial=initial, distinct_sites=len(visits))
        digest.update((json.dumps([current, regs], separators=(',', ':'))+'\n').encode())
        if op == 'CH':
            return dict(status='HALT', source_steps=tick, registers=regs)
        if op == 'CI':
            regs[reg] += 1
        elif positive:
            regs[reg] -= 1
        current = edges[current][int(positive) if op == 'CD' else 0]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--sites', type=Path, required=True)
    ap.add_argument('--failures', type=Path, required=True)
    ap.add_argument('--initial', default='3,0,0,0,3,0,0,0,0')
    ap.add_argument('--limit', type=int, default=1000000)
    ap.add_argument('--output', type=Path, required=True)
    a = ap.parse_args()
    sites = json.loads(a.sites.read_text())
    failures = json.loads(a.failures.read_text())
    targets = {(x['site_index'], bool(x['positive'])) for x in failures}
    initial = list(map(int, a.initial.split(',')))
    assert len(initial) == 9 and min(initial) >= 0
    result = execute(sites, initial, targets, a.limit)
    result['sites_sha256'] = hashlib.sha256(a.sites.read_bytes()).hexdigest()
    result['scope'] = ('Exact reachability in the reference register program from the stated seed. '
                       'A binary frame simulation is a separate check.')
    a.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()

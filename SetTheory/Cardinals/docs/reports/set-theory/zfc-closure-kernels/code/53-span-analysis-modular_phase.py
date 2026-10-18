#!/usr/bin/env python3
"""Finite abstract interpretation with exact small values and periodic tails.

The domain partitions all natural numbers: 0,...,K-1 and
{n >= K : n = r mod M}, for 0 <= r < M.  Product joins forget
correlations.  A checked post-fixpoint proves exclusions by induction;
an enabled guard is not asserted reachable.  This is not a Lean proof.
"""
from __future__ import annotations
import argparse
from collections import defaultdict, deque
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import sys
import time


def analyse(graph, exact, modulus):
    sites, cases, targets, first = graph
    count = exact + modulus
    all_bits = (1 << count) - 1
    def cls(n):
        return n if n < exact else exact + n % modulus
    inc = [1 << cls(i + 1) for i in range(exact)]
    dec = [0 if i == 0 else 1 << cls(i - 1) for i in range(exact)]
    for residue in range(modulus):
        inc.append(1 << (exact + (residue + 1) % modulus))
        dec.append((1 << (exact + (residue - 1) % modulus)) |
                   ((1 << (exact - 1)) if residue == exact % modulus else 0))

    @lru_cache(None)
    def image(mask, decrement):
        result = 0
        choices = dec if decrement else inc
        while mask:
            bit = mask & -mask
            result |= choices[bit.bit_length() - 1]
            mask -= bit
        return result

    def transfer(values, case):
        _, _, op, reg, zero = case
        if op not in ('CI', 'CD'):
            return values
        old = values[reg]
        if op == 'CI':
            new = image(old, False)
        elif zero:
            if not old & 1:
                return None
            new = 1
        else:
            if not old & (all_bits ^ 1):
                return None
            new = image(old & (all_bits ^ 1), True)
        return values[:reg] + (new,) + values[reg + 1:]

    outgoing = defaultdict(list)
    for i, case in enumerate(cases):
        outgoing[case[0]].append(i)
    inv = [None] * len(sites)
    inv[first] = (1,) * 9
    pending = deque([first])
    in_queue = {first}
    pops = 0
    started = time.monotonic()
    while pending:
        site = pending.popleft()
        in_queue.remove(site)
        pops += 1
        for i in outgoing[site]:
            target = targets[i]
            if target is None:
                continue
            post = transfer(inv[site], cases[i])
            if post is None:
                continue
            old = inv[target]
            new = post if old is None else tuple(a | b for a, b in zip(old, post))
            if old != new:
                inv[target] = new
                if target not in in_queue:
                    pending.append(target)
                    in_queue.add(target)

    # Independent-of-worklist certificate gate: initial inclusion and closure.
    assert all(mask & 1 for mask in inv[first])
    excluded = []
    edges = 0
    for i, (case, target) in enumerate(zip(cases, targets)):
        before = inv[case[0]]
        post = None if before is None else transfer(before, case)
        if post is None:
            excluded.append(i)
        elif target is not None:
            assert inv[target] is not None
            assert all(a & ~b == 0 for a, b in zip(post, inv[target]))
            edges += 1
    encoded = json.dumps(inv, separators=(',', ':')).encode()
    return {
        'exact_threshold': exact, 'modulus': modulus, 'classes': count,
        'postfix_certificate': 'PASS', 'excluded_cases': excluded,
        'possible_leaves': sum(x is not None for x in inv),
        'enabled_nonhalt_edges': edges, 'worklist_pops': pops,
        'invariant_sha256': hashlib.sha256(encoded).hexdigest(),
        'elapsed_seconds': time.monotonic() - started,
    }, inv


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    base = args.repo / 'Computability/BusyBeaver/Research/ZFC'
    sys.path.insert(0, str(base))
    import permutation252_phase_analysis as upstream
    prog = args.repo / 'lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v'
    raw = prog.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == upstream.PROG_SHA
    graph = upstream.program_graph(raw)
    results = []
    strongest = None
    for exact in (2, 4, 8, 16, 32):
        for modulus in (1, 2, 4, 8, 16):
            result, inv = analyse(graph, exact, modulus)
            results.append(result)
            strongest = inv
            print(json.dumps(result), flush=True)
    out = {'scope': 'Sound finite natural-value overapproximation; no modified TM or state bound.',
           'program_sha256': hashlib.sha256(raw).hexdigest(),
           'prior_exclusions': upstream.EXCLUDED, 'results': results,
           'all_exclusions': sorted(set(i for r in results for i in r['excluded_cases'])),
           'strongest_invariant': strongest}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + '\n')


if __name__ == '__main__':
    main()

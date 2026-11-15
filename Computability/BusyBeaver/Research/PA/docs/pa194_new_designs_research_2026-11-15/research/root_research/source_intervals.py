#!/usr/bin/env python3
"""Compute and independently check a sound source-program interval invariant.

This is newly reconstructed after the temporary work volume was lost. It is not
the byte-for-byte previous script or certificate. Upper bounds widen to infinity
when an existing abstract state would increase; every resulting edge is checked.
"""
from collections import deque
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent
PROGRAM = ROOT.parent / 'reductions/inputs/pa194.instructions.json'

def includes(outer, inner):
    return all(a <= c and (b is None or (d is not None and d <= b))
               for (a, b), (c, d) in zip(outer, inner))

def successors(ins, abstract):
    opcode = ins[0]
    if opcode == 'halt':
        return []
    if opcode == 'jump':
        return [(ins[1], abstract, 'jump')]
    reg = ins[1]
    lo, hi = abstract[reg]
    if opcode == 'inc':
        result = list(abstract)
        result[reg] = lo + 1, None if hi is None else hi + 1
        return [(ins[2], tuple(result), 'inc')]
    assert opcode == 'dec'
    answer = []
    # Resolved source command is [dec, register, zero_target, positive_target].
    if lo == 0:
        result = list(abstract)
        result[reg] = 0, 0
        answer.append((ins[2], tuple(result), 'zero'))
    if hi is None or hi >= 1:
        result = list(abstract)
        result[reg] = max(lo, 1) - 1, None if hi is None else hi - 1
        answer.append((ins[3], tuple(result), 'positive'))
    return answer

def join_widen(old, new):
    if old is None:
        return new
    result = []
    for (a, b), (c, d) in zip(old, new):
        upper = b if b is None or (d is not None and d <= b) else None
        result.append((min(a, c), upper))
    return tuple(result)

def main():
    program = json.loads(PROGRAM.read_text())
    assert len(program) == 3673
    seed = tuple((2, 2) if r == 0 else (0, 0) for r in range(9))
    invariant = [None] * len(program)
    invariant[25] = seed
    queue, queued = deque([25]), {25}
    updates = 0
    while queue:
        pc = queue.popleft()
        queued.remove(pc)
        for nxt, abstract, kind in successors(program[pc], invariant[pc]):
            assert 0 <= nxt < len(program)
            joined = join_widen(invariant[nxt], abstract)
            if joined != invariant[nxt]:
                invariant[nxt] = joined
                updates += 1
                if nxt not in queued:
                    queue.append(nxt)
                    queued.add(nxt)
    # The closure check, not the heuristic computation, is the certificate's
    # essential safety property. Initial state and every possible abstract edge
    # are included, and all intervals are valid natural-number intervals.
    assert includes(invariant[25], seed)
    checked_edges = 0
    for pc, abstract in enumerate(invariant):
        if abstract is None:
            continue
        assert len(abstract) == 9
        for lo, hi in abstract:
            assert lo >= 0 and (hi is None or lo <= hi)
        for nxt, post, kind in successors(program[pc], abstract):
            assert invariant[nxt] is not None and includes(invariant[nxt], post)
            checked_edges += 1
    unreachable = [i for i, abstract in enumerate(invariant) if abstract is None]
    forced_zero, forced_positive = [], []
    for pc, ins in enumerate(program):
        if ins[0] == 'dec' and invariant[pc] is not None:
            lo, hi = invariant[pc][ins[1]]
            if hi == 0:
                forced_zero.append({'site': pc, 'register': ins[1]})
            if lo >= 1:
                forced_positive.append({'site': pc, 'register': ins[1]})
    receipt = {
        'evidence_status': 'Fresh reconstructed interval fixed point and full postfixedness check',
        'source_sha256': hashlib.sha256(PROGRAM.read_bytes()).hexdigest(),
        'sites': len(program), 'initial_site': 25, 'initial_registers': [2] + [0] * 8,
        'updates': updates, 'checked_edges': checked_edges,
        'abstractly_unreachable': unreachable,
        'forced_zero_decrements': forced_zero,
        'forced_positive_decrements': forced_positive,
        'scope': 'A sound overapproximation of the calibrated source execution, not a proof of PA consistency.',
        'invariant': invariant,
    }
    path = ROOT / 'intervals.json'
    path.write_text(json.dumps(receipt, separators=(',', ':')) + '\n')
    print(json.dumps({k: v for k, v in receipt.items() if k != 'invariant'}, indent=2))

if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Independent checker for the supplied natural-number interval invariant."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent

def main():
    program_path = ROOT.parent / 'reductions/inputs/pa194.instructions.json'
    cert_path = ROOT / 'intervals.json'
    cert = json.loads(cert_path.read_text())
    assert hashlib.sha256(program_path.read_bytes()).hexdigest() == cert['source_sha256']
    code = json.loads(program_path.read_text())
    invariant = cert['invariant']
    assert len(code) == len(invariant) == 3673
    for state in invariant:
        if state is not None:
            assert len(state) == 9
            for lo, hi in state:
                assert type(lo) is int and lo >= 0
                assert hi is None or type(hi) is int and hi >= lo
    initial = [2] + [0] * 8
    assert invariant[25] is not None
    for value, (lo, hi) in zip(initial, invariant[25]):
        assert lo <= value and (hi is None or value <= hi)
    checked = 0
    for pc, state in enumerate(invariant):
        if state is None:
            continue
        ins = code[pc]
        op = ins[0]
        edges = []
        if op == 'halt':
            assert len(ins) == 1
        elif op == 'jump':
            assert len(ins) == 2
            edges.append((ins[1], state))
        elif op == 'inc':
            assert len(ins) == 3
            reg = ins[1]
            out = [list(x) for x in state]
            out[reg][0] += 1
            if out[reg][1] is not None:
                out[reg][1] += 1
            edges.append((ins[2], out))
        else:
            assert op == 'dec' and len(ins) == 4
            reg = ins[1]
            lo, hi = state[reg]
            if lo == 0:
                out = [list(x) for x in state]
                out[reg] = [0, 0]
                edges.append((ins[2], out))
            if hi is None or hi > 0:
                out = [list(x) for x in state]
                out[reg] = [max(lo - 1, 0), None if hi is None else hi - 1]
                edges.append((ins[3], out))
        for dest, out in edges:
            assert 0 <= dest < len(code) and invariant[dest] is not None
            for (lo, hi), (postlo, posthi) in zip(invariant[dest], out):
                assert lo <= postlo
                assert hi is None or posthi is not None and posthi <= hi
            checked += 1
    unreachable = [i for i, state in enumerate(invariant) if state is None]
    forced_zero = [{'site': i, 'register': code[i][1]} for i, state in enumerate(invariant)
                   if state is not None and code[i][0] == 'dec' and state[code[i][1]][1] == 0]
    assert checked == cert['checked_edges'] == 4774
    assert unreachable == cert['abstractly_unreachable'] == [8, 3635, 3636]
    assert forced_zero == cert['forced_zero_decrements'] == [
        {'site': 7, 'register': 6}, {'site': 3634, 'register': 1}]
    receipt = {
        'status': 'PASS',
        'evidence_status': 'Fresh independent check of initial inclusion, all abstract successor inclusions, and stated exclusions',
        'source_sha256': cert['source_sha256'],
        'certificate_sha256': hashlib.sha256(cert_path.read_bytes()).hexdigest(),
        'checked_edges': checked,
        'unreachable_sites': unreachable,
        'forced_zero_decrements': forced_zero,
    }
    (ROOT / 'interval_replay_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))

if __name__ == '__main__':
    main()

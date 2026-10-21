#!/usr/bin/env python3
"""Rebuild and audit K215-R41; optionally rederive every symbolic runtime case.

The default is the complete runtime check. --quick checks only exact finite
construction, dense renaming, graph differences, and blank initialization.
Neither mode runs a proof-assistant kernel or proves the inherited calculus.
"""
from pathlib import Path
from collections import deque
import argparse, hashlib, json, subprocess, sys, time

ROOT = Path(__file__).resolve().parents[1]
NATIVE_SHA = '8cfb95be77f8f8819ac7dc5c92297cf32b5104cbdf22aea925ab38de9c4443b9'
SOURCE_SHA = '46ab3fdabc6ade3c6e4b5f08a0a59af66eb96f3992124ab6b71b8c3f1a05bf35'
DENSE_SHA = '27a2a4f452f9fcb1e84ba6f78d0f952ea438eca00d415cc6b0ef4298d35086a4'
PHY = (6, 2, 0, 4, 3, 7, 8, 5, 1)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def table(path):
    rows = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, bit, w, direction, target = line.split()
        key = int(q), int(bit)
        assert key not in rows and direction in ('L', 'R')
        assert int(bit) in (0, 1) and int(w) in (0, 1)
        rows[key] = int(w), 1 if direction == 'R' else -1, int(target)
    return rows

def canonical(rows, halt=254):
    mapping, queue, encoded = {0: 0}, [0], []
    for q in queue:
        for bit in (0, 1):
            w, d, z = rows[q, bit]
            if z != halt and z not in mapping:
                mapping[z] = len(mapping)
                queue.append(z)
            encoded.append((mapping[q], bit, w, d, -1 if z == halt else mapping[z]))
    assert len(mapping) == len({q for q, _ in rows})
    return encoded

def expected_seed():
    head, gap = -8, 1
    registers = [4, 0, 0, 0, 0, 0, 0, 0, 0]
    physical = [None] * 9
    for i, j in enumerate(PHY):
        physical[j] = registers[i]
    header = head + 64 + gap
    support = {head - 1, header}
    pos = header + 1
    for value in physical + [1] * 40:
        pos += 1
        support.update(range(pos, pos + value + 1))
        pos += value + 1
    assert len(support) == 95
    return 84, head, support

def blank_prefix(rows):
    q, head, support = 0, 0, set()
    visited = set()
    for tick in range(95714):
        bit = int(head in support)
        assert (q, bit) in rows, ('early halt', tick, q)
        visited.add((q, bit))
        w, direction, q = rows[q, bit]
        if w:
            support.add(head)
        else:
            support.discard(head)
        head += direction
    assert (q, head, support) == expected_seed()
    return dict(steps=95714, state=q, head=head, header=57, gap=1,
                registers=[4, 0, 0, 0, 0, 0, 0, 0, 0],
                spare_count=40, spare_value=1, one_cells=sorted(support),
                zero_exterior=True, visited_rows=len(visited))

def main():
    assert __debug__ and not sys.flags.optimize, 'Run without -O'
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True,
                    help='A fresh directory for this verification run')
    ap.add_argument('--quick', action='store_true')
    args = ap.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    native = ROOT / 'machine/k215r.native.tm'
    dense = ROOT / 'machine/k215r.tm'
    source = ROOT / 'machine/sites215r.json'
    assert (digest(native), digest(source), digest(dense)) == (NATIVE_SHA, SOURCE_SHA, DENSE_SHA)
    command = [sys.executable, '-B', str(ROOT / 'code/reconstruct_rotated.py'),
               '--baseline', str(ROOT / 'baseline'),
               '--recipe', str(ROOT / 'machine/recipe.json'),
               '--output', str(out / 'rebuilt')]
    with (out / 'reconstruction.log').open('w') as log:
        subprocess.run(command, check=True, stdout=log, stderr=subprocess.STDOUT)
    for original, rebuilt in [(native, 'candidate.native.tm'),
                              (dense, 'candidate.tm'), (source, 'sites.json')]:
        assert original.read_bytes() == (out / 'rebuilt' / rebuilt).read_bytes()
    rows = table(native)
    assert len(rows) == 430 and len({q for q, _ in rows}) == 215
    assert all((q, b) in rows for q, _ in rows for b in (0, 1))
    assert {z for w, d, z in rows.values()} - {q for q, _ in rows} == {254}
    seed = blank_prefix(rows)
    graph = canonical(rows)
    distinct = {}
    for name in ('k215.native.tm', 'commands120.native.tm', 'composed.native.tm'):
        other = canonical(table(ROOT / 'baseline' / name))
        distinct[name] = graph != other
        assert distinct[name], ('state renaming of', name)
    receipt = dict(status='FINITE_BINDING_AND_BLANK_PASS',
                   scope='Finite reconstruction, graph comparison, and exact complete blank prefix only.',
                   native_sha256=NATIVE_SHA, dense_sha256=DENSE_SHA,
                   source_sha256=SOURCE_SHA, working_states=215, rows=430,
                   graph_distinctness=distinct, blank=seed)
    if not args.quick:
        command = [sys.executable, '-B', str(ROOT / 'runtime/validate_native.py'),
                   str(native), str(source), str(out / 'runtime')]
        started = time.monotonic()
        with (out / 'runtime.log').open('w') as log:
            subprocess.run(command, check=True, stdout=log, stderr=subprocess.STDOUT)
        result = json.loads((out / 'runtime/runtime.json').read_text())
        cases = json.loads((out / 'runtime/runtime_cases.json').read_text())
        assert result['status'] == 'UNIVERSAL_MATHEMATICAL_PASS'
        assert result['proved_cases'] == result['expected_cases'] == len(cases) == 6176
        assert result['working_states'] == 215 and not result['failures']
        assert result['table_sha256'] == NATIVE_SHA and result['sites_sha256'] == SOURCE_SHA
        assert all(c['duration'][0] > 0 and all(v >= 0 for v in c['duration']) for c in cases)
        receipt.update(status='COMPLETE_SYMBOLIC_RUNTIME_AND_BLANK_PASS',
                       scope='All-natural symbolic primitive proof plus exact source and blank binding; ordinary mathematical evidence, not a proof-assistant kernel check.',
                       cases=len(cases), symbolic_rules=sum(c['symbolic_steps'] for c in cases),
                       minimum_duration_constant=min(c['duration'][0] for c in cases),
                       runtime_seconds=time.monotonic() - started)
    assert (digest(native), digest(source), digest(dense)) == (NATIVE_SHA, SOURCE_SHA, DENSE_SHA)
    (out / 'verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: v for k, v in receipt.items() if k != 'blank'}, indent=2))

if __name__ == '__main__':
    main()

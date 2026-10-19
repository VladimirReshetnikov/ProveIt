#!/usr/bin/env python3
"""Independent exact-table and local proof audit for the 243 -> 242 reduction.

The finite check covers every transition row and every bit read by the two
exceptional blocks. The accompanying mathematical argument lifts these facts
to arbitrary function tapes by induction; this is not a proof-assistant run.
"""
import argparse, hashlib, json
from pathlib import Path

BASE_SHA = '4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300'
BASE = Path(__file__).resolve().parents[1] / 'reference/combined243/zfc_combined243_old.tm'

def read(path):
    t = {}
    start = None
    for line in path.read_text().splitlines():
        if line.startswith('#! start '): start = int(line.split()[-1])
        if not line or line.startswith('#'): continue
        q, b, w, d, r = line.split()
        q, b, w, r = map(int, (q, b, w, r))
        assert b in (0, 1) and w in (0, 1) and d in ('L', 'R')
        assert (q, b) not in t
        t[q, b] = (w, d, r)
    return t, start

def encode(t, start):
    return '#! start ' + str(start) + '\n' + ''.join(
        f'{q} {b} {w} {d} {r}\n' for (q, b), (w, d, r) in sorted(t.items()))

def symbolic_run(t, bits, steps):
    # Every other cell is a distinct symbolic variable, preserved in the map.
    initial = dict(bits)
    tape = dict(bits)
    q, h = 11, 0
    trace = []
    for _ in range(steps):
        bit = tape.get(h, ('cell', h))
        assert bit in (0, 1), ('unconstrained read', q, h, bit)
        w, d, r = t[q, bit]
        trace.append([q, h, bit, w, d, r])
        tape[h] = w
        q, h = r, h + (1 if d == 'R' else -1)
    changed = {k: v for k, v in tape.items() if v != initial.get(k, ('cell', k))}
    return (q, h, changed), trace

def audit(old, new):
    oldstates = {q for q, _ in old}
    newstates = {q for q, _ in new}
    assert len(oldstates) == 243 and len(newstates) == 242
    assert newstates == oldstates - {15}
    assert set(new) == {(q, b) for q in newstates for b in (0, 1)}
    assert {r for w, d, r in new.values()} - newstates == {254}
    assert {k for k in new if new[k] != old[k]} == {(11, 0), (27, 1)}
    assert old[11, 0] == (0, 'R', 15)
    assert old[15, 0] == (0, 'R', 21) and old[15, 1] == (1, 'R', 22)
    assert new[11, 0] == (0, 'R', 27) and new[27, 1] == (1, 'R', 22)
    inbound = lambda q: [(k, v) for k, v in sorted(old.items()) if v[2] == q]
    assert [k for k, v in inbound(15)] == [(11, 0)]
    # I(q,h,t): q in {18,47,65} -> t(h-1)=0; q=27 -> t(h)=0.
    protected = {18, 47, 65}
    witnesses = {}
    for q in sorted(protected):
        rows = inbound(q)
        assert rows and all(v[:2] == (0, 'R') for k, v in rows)
        witnesses[str(q)] = [[*k, *v] for k, v in rows]
    rows27 = inbound(27)
    assert rows27 and all(k[0] in protected and v[1] == 'L' for k, v in rows27)
    # The written cell differs from the new head; old I supplies the zero.
    assert 95 not in protected | {27}
    blocks = []
    for bit, newtime in [(0, 4), (1, 2)]:
        eo, to = symbolic_run(old, {0: 0, 1: bit}, 2)
        en, tn = symbolic_run(new, {0: 0, 1: bit}, newtime)
        assert eo == en == (21 if bit == 0 else 22, 2, {})
        assert all(row[-1] != 254 for row in to + tn)
        blocks.append(dict(next_bit=bit, old_steps=2, new_steps=newtime,
                           old_trace=to, new_trace=tn, common_endpoint=list(eo),
                           unmentioned_cells_preserved=True))
    ordinary = []
    excluded = []
    for key in sorted(new):
        if key == (11, 0): continue
        if key == (27, 1):
            excluded.append(dict(row=list(key), reason='Impossible at old reachable checkpoints by I.'))
            continue
        assert new[key] == old[key]
        assert old[key][2] != 15
        ordinary.append(list(key))
    assert len(ordinary) == 482
    return dict(status='PASS_EXACT_TABLE_INVARIANT_AND_BLOCK_AUDIT',
                working_states=242, total_rows=484, ordinary_rows_checked=len(ordinary),
                invariant_left_zero_incoming=witnesses,
                invariant_current_zero_incoming27=[[*k, *v] for k, v in rows27],
                removed_state15_incoming=[[*k, *v] for k, v in inbound(15)],
                exceptional_blocks=blocks, impossible_old_rows=excluded,
                old_initial_state=95, new_initial_state=95, halt_state=254,
                mathematical_scope='Whole-tape positive-block halting equivalence from state95 with arbitrary head and arbitrary binary function tape.',
                proof_assistant_executed=False,
                limitation='The ordinary induction argument in the report is part of the proof; the Python audit does not certify the inherited consistency calibration.')

def main():
    if not __debug__: raise RuntimeError('Python assertions must remain enabled.')
    ap = argparse.ArgumentParser()
    ap.add_argument('--baseline', type=Path, default=BASE)
    ap.add_argument('--output', type=Path, required=True)
    a = ap.parse_args()
    assert hashlib.sha256(a.baseline.read_bytes()).hexdigest() == BASE_SHA
    old, start = read(a.baseline)
    assert start == 95
    new = {k: v for k, v in old.items() if k[0] != 15}
    new[11, 0] = (0, 'R', 27)
    new[27, 1] = (1, 'R', 22)
    evidence = audit(old, new)
    a.output.mkdir(parents=True, exist_ok=True)
    raw = encode(new, 95)
    (a.output / 'zfc_return242_old.tm').write_text(raw)
    order = [95] + sorted({q for q, b in new} - {95})
    mapping = {q: i for i, q in enumerate(order)} | {254: len(order)}
    canonical = {(mapping[q], b): (w, d, mapping[r]) for (q, b), (w, d, r) in new.items()}
    text = encode(canonical, 0)
    (a.output / 'zfc_return242.tm').write_text(text)
    (a.output / 'renumbering.json').write_text(json.dumps(dict(old_to_canonical=mapping, canonical_to_old=order), indent=2) + '\n')
    # Re-read the actual written objects and check the bijection in both ways.
    newread, newstart = read(a.output / 'zfc_return242_old.tm')
    canread, canstart = read(a.output / 'zfc_return242.tm')
    assert newread == new and newstart == 95 and canread == canonical and canstart == 0
    inverse = {v: k for k, v in mapping.items()}
    assert {(inverse[q], b): (w, d, inverse[r]) for (q, b), (w, d, r) in canread.items()} == new
    evidence.update(baseline_sha256=BASE_SHA, inherited_sha256=hashlib.sha256(raw.encode()).hexdigest(),
                    canonical_sha256=hashlib.sha256(text.encode()).hexdigest(),
                    canonical_start=0, canonical_dispatcher=mapping[96], canonical_halt=mapping[254])
    (a.output / 'local-proof-audit.json').write_text(json.dumps(evidence, indent=2) + '\n')
    print(json.dumps({k:v for k,v in evidence.items() if k not in ('exceptional_blocks',)}, indent=2))

if __name__ == '__main__': main()

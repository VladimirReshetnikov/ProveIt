#!/usr/bin/env python3
"""Deterministically construct the 242-state table from the exact 243 baseline."""
from pathlib import Path
import hashlib, json

ROOT = Path(__file__).resolve().parents[1]
BASE_SHA = '4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300'

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def load(path):
    table, start = {}, None
    for line in Path(path).read_text(encoding='ascii').splitlines():
        if line.startswith('#! start '):
            assert start is None
            start = int(line.split()[-1])
        elif line and not line.startswith('#'):
            q,b,w,d,t = line.split()
            q,b,w,t = map(int,(q,b,w,t))
            assert b in (0,1) and w in (0,1) and d in ('L','R')
            assert (q,b) not in table
            table[q,b] = w,d,t
    states = {q for q,b in table}
    assert start in states and set(table) == {(q,b) for q in states for b in (0,1)}
    return table, start

def encode(table,start):
    return '#! start '+str(start)+'\n'+''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(table.items()))

def main():
    if not __debug__: raise RuntimeError('Run with Python assertions enabled.')
    base = ROOT/'reference/zfc_combined243_old.tm'
    assert digest(base) == BASE_SHA
    old,start = load(base)
    assert start == 95 and len(old) == 486
    new = dict(old)
    assert old[11,0] == (0,'R',15)
    assert old[15,0] == (0,'R',21) and old[15,1] == (1,'R',22)
    assert old[27,0] == (0,'L',32) and old[27,1] == (1,'R',39)
    del new[15,0],new[15,1]
    new[11,0] = 0,'R',27
    new[27,1] = 1,'R',22
    states = {q for q,b in new}
    assert len(states)==242 and {t for w,d,t in new.values()} - states == {254}
    order = [95]+sorted(states-{95})
    mapping = {q:i for i,q in enumerate(order)} | {254:242}
    canonical = {(mapping[q],b):(w,d,mapping[t]) for (q,b),(w,d,t) in new.items()}
    target = ROOT/'machine'
    target.mkdir(exist_ok=True)
    (target/'zfc_context242_old.tm').write_text(encode(new,95),encoding='ascii')
    (target/'zfc_context242.tm').write_text(encode(canonical,0),encoding='ascii')
    (target/'renumbering.json').write_text(json.dumps({'old_to_canonical':mapping,'canonical_to_old':order,'halt_old':254,'halt_canonical':242},indent=2)+'\n')
    result = dict(status='CONSTRUCTED',working_states=242,transitions=484,alphabet=[0,1],
        start=0,halt=242,inherited_start=95,inherited_halt=254,dispatcher=mapping[96],
        input_sha256=BASE_SHA,removed_state=15,changed_retained_rows=[[11,0],[27,1]],
        canonical_sha256=digest(target/'zfc_context242.tm'),inherited_sha256=digest(target/'zfc_context242_old.tm'))
    (ROOT/'evidence/construction.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()

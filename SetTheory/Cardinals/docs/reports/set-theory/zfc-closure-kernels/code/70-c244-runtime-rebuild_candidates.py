#!/usr/bin/env python3
"""Rebuild the three discovered 244-state tables from the pinned old labels."""
from pathlib import Path
import hashlib
import json

HERE=Path(__file__).resolve().parent
PIN='f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267'

def encode(table,start):
    return f'#! start {start}\n'+''.join(
        f'{q} {b} {w} {d} {t}\n'
        for (q,b),(w,d,t) in sorted(table.items()))

def main():
    assert __debug__
    path=HERE/'reference/zfc245_old.tm'
    assert hashlib.sha256(path.read_bytes()).hexdigest()==PIN
    original={}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q,b,w,d,t=line.split()
        original[int(q),int(b)]=int(w),d,int(t)
    variants=[(122,167),(149,167),(149,170)]
    records=[]
    for i,(removed,repair) in enumerate(variants,1):
        table={k:v for k,v in original.items() if k[0]!=removed}
        table[92,1]=original[removed,1]
        table={k:(w,d,92 if t==removed else t) for k,(w,d,t) in table.items()}
        table[repair,1]=(1,'L',151)
        states={q for q,b in table}
        assert len(states)==244 and len(table)==488
        assert {t for w,d,t in table.values()}-states=={254}
        order=[95]+sorted(states-{95})
        renumber={q:j for j,q in enumerate(order)}|{254:244}
        dense={(renumber[q],b):(w,d,renumber[t]) for (q,b),(w,d,t) in table.items()}
        oldtext=encode(table,95)
        text=encode(dense,0)
        (HERE/f'candidate_{i}_244_old.tm').write_text(oldtext)
        (HERE/f'candidate_{i}_244.tm').write_text(text)
        (HERE/f'candidate_{i}_renumbering.json').write_text(json.dumps(
            dict(canonical_to_old=order,old_to_canonical=renumber,halt_old=254,halt_canonical=244),indent=2)+'\n')
        records.append(dict(candidate=i,removed_state=removed,repair_source=repair,
                            working_states=244,start_old=95,start_canonical=0,
                            halt_old=254,halt_canonical=244,
                            old_sha256=hashlib.sha256(oldtext.encode()).hexdigest(),
                            canonical_sha256=hashlib.sha256(text.encode()).hexdigest()))
    (HERE/'rebuild_manifest.json').write_text(json.dumps(dict(
        status='PASS_EXACT_REBUILD',baseline_old_sha256=PIN,candidates=records),indent=2)+'\n')
    print(json.dumps(records,indent=2))

if __name__=='__main__':
    main()

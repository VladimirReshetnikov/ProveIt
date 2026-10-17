#!/usr/bin/env python3
"""Construct the known runtime252 table with explicit new blank start.

Source labels are retained during certificate replay. The distributable
table has working states 0,...,251, start 0 and terminal state 252.
"""
from pathlib import Path
import hashlib,json
import macro252 as M

def generate(destination=None):
    root=Path(__file__).resolve().parents[1]
    destination=Path(destination) if destination is not None else root/'machines'
    destination.mkdir(parents=True,exist_ok=True)
    table=M.m.rows();working=sorted({q for q,b in table})
    assert len(working)==252 and len(table)==504
    order=[64]+[q for q in working if q!=64]
    mapping={q:i for i,q in enumerate(order)};mapping[254]=252
    assert set(mapping.values())==set(range(253))
    assert all(t in mapping for w,d,t in table.values())
    original={}
    for line in (M.m.REPO/'ZF/m254/machine/zfc_254.tm').read_text().splitlines():
        if line and not line.startswith('#'):
            q,b,w,d,t=line.split();original[int(q),int(b)]=int(w),d,int(t)
    changes=[(q,b,original[q,b],table[q,b]) for q,b in table if original[q,b]!=table[q,b]]
    assert changes==[(3,0,(0,'L',5),(0,'L',48))]
    assert set(original)-set(table)=={(q,b) for q in (5,8) for b in (0,1)}
    old='# Known runtime252 table; original 254-machine labels.\n# Blank start: 64. Terminal: 254. Working states: 252.\n'
    old+=''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(table.items()))
    new='# runtime252 with the emergent blank bootstrap studied in this report.\n# Working states: 0..251. Blank start: 0. Terminal: 252. Alphabet: 0,1.\n'
    for q in order:
        for b in (0,1):
            w,d,t=table[q,b];new+=f'{mapping[q]} {b} {w} {d} {mapping[t]}\n'
    (destination/'runtime252-old-labels.tm').write_text(old)
    (destination/'runtime252.tm').write_text(new)
    meta={'working_states':252,'alphabet':[0,1],'blank_symbol':0,'start':0,'terminal':252,
          'source_start':64,'source_terminal':254,'removed_source_states':[5,8],
          'changed_source_transition':{'state':3,'read':0,'original':[0,'L',5],'replacement':[0,'L',48]},
          'old_to_new':mapping,'sha256':hashlib.sha256(new.encode()).hexdigest(),
          'old_labels_sha256':hashlib.sha256(old.encode()).hexdigest()}
    (destination/'old_to_new.json').write_text(json.dumps(meta,indent=2)+'\n')
    return meta

if __name__=='__main__':
    out=generate();print({k:v for k,v in out.items() if k!='old_to_new'})

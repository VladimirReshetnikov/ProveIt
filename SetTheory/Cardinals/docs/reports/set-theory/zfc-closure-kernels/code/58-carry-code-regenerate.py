#!/usr/bin/env python3
"""Regenerate and compare the two frozen 250-state transition tables."""
from pathlib import Path
import hashlib
import json

ROOT=Path(__file__).resolve().parents[1]
BASE_SHA='939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713'
OLD_SHA='fd455304bad82a6da7ab83149352d0b1db27557582c4cc6312de003c96ff4e43'
CANON_SHA='0626819c4842f224001e7685366d8061897a7bc9470c015129a1d1cf22efb36e'

def parse(raw):
    rows={};start=None
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):start=int(line.split()[-1])
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t))
        assert b in(0,1) and w in(0,1) and d in('L','R') and(q,b)not in rows
        rows[q,b]=(w,d,t)
    states={q for q,b in rows}
    assert start in states and set(rows)=={(q,b)for q in states for b in(0,1)}
    return rows,start

def encode(table,start):
    return ('#! start '+str(start)+'\n'+''.join(f'{q} {b} {w} {d} {t}\n' for(q,b),(w,d,t)in sorted(table.items()))).encode('ascii')

def construct():
    raw=(ROOT/'sources/baseline252_old.tm').read_bytes()
    assert hashlib.sha256(raw).hexdigest()==BASE_SHA
    baseline,start=parse(raw);assert start==64 and len(baseline)==504
    table={k:v for k,v in baseline.items()if k[0]not in(43,59,85)}
    patch={(30,1):(0,'R',95),(75,0):(1,'R',255),(75,1):(1,'L',63),
           (97,0):(1,'R',83),(97,1):(1,'L',131),(109,0):(0,'R',75),
           (131,0):(0,'L',48),(255,0):(1,'L',97),(255,1):(1,'L',131)}
    table.update(patch)
    states={q for q,b in table}
    assert len(states)==250 and len(table)==500
    assert states==(set(range(254))-{5,8,43,59,85})|{255}
    assert {t for w,d,t in table.values()}-states=={254}
    old=encode(table,97);assert hashlib.sha256(old).hexdigest()==OLD_SHA
    order=[97]+sorted(states-{97});mapping={q:i for i,q in enumerate(order)}
    canonical={(mapping[q],b):(w,d,250 if t==254 else mapping[t])for(q,b),(w,d,t)in table.items()}
    canon=encode(canonical,0);assert hashlib.sha256(canon).hexdigest()==CANON_SHA
    return baseline,table,canonical,mapping,old,canon

def verify():
    baseline,table,canonical,mapping,old,canon=construct()
    assert old==(ROOT/'machine/zfc_prefix250_old.tm').read_bytes()
    assert canon==(ROOT/'machine/zfc_prefix250.tm').read_bytes()
    labels=json.loads((ROOT/'machine/renumbering.json').read_text())
    assert labels['old_to_canonical']=={str(k):v for k,v in mapping.items()}
    assert labels['canonical_sha256']==CANON_SHA and labels['old_sha256']==OLD_SHA
    seen=set();pending=[0]
    while pending:
        q=pending.pop()
        if q==250 or q in seen:continue
        seen.add(q);pending.extend(canonical[q,b][2]for b in(0,1))
    changed=[{'state':q,'read':b,'before':list(baseline[q,b]),'after':list(a)}for(q,b),a in table.items()if(q,b)in baseline and baseline[q,b]!=a]
    result={'status':'PASS','working_states':250,'rows':500,'start':0,'halt':250,'dispatch':mapping[96],
            'graph_reachable_working_states':len(seen),'canonical_sha256':CANON_SHA,'old_sha256':OLD_SHA,
            'removed_working_states':[43,59,85],'added_working_states':[255],'changed_retained_rows':changed,
            'halting_rows':[{'state':q,'read':b,'transition':list(v)}for(q,b),v in canonical.items()if v[2]==250]}
    return result

if __name__=='__main__':
    if not __debug__:raise RuntimeError('Run Python without -O; assertions are required.')
    print(json.dumps(verify(),indent=2))

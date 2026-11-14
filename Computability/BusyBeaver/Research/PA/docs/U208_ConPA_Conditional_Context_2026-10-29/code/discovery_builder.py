#!/usr/bin/env python3
"""Construct and independently check the two-history-bit U208 reduction.

No source change.  The proof is a positive-block simulation of the frozen
209-state Joint machine on every tape when started in native state 0.
"""
import argparse,hashlib,json
from pathlib import Path

PARENT_SHA='d0a155d3c683789f3bf5327c0cfb2a0cfd78076af8f1654d4ca426ccbb604d16'
COMPAT_SHA='4564c4876f9b18725bfb3505ec1f50d1ebce572502f2c6381ad673ecfdc3c3e1'

def read(path):
    table={}
    for l in Path(path).read_text().splitlines():
        if not l or l.startswith('#'):continue
        q,b,w,d,z=l.split();key=int(q),int(b)
        assert key not in table
        assert d in ('L','R')
        table[key]=int(w),1 if d=='R' else -1,int(z)
    return table

def encode(table):
    return '#! start 0\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n' for (q,b),(w,d,z) in sorted(table.items()))

def incoming(t,q):
    return [(p,b,w,d) for (p,b),(w,d,z) in sorted(t.items()) if z==q]

def check_census(t,n,halt):
    states={q for q,b in t}
    assert len(states)==n and len(t)==2*n and 0 in states and halt not in states
    for q in states:
        for b in (0,1):
            w,d,z=t[q,b];assert w in (0,1) and d in (-1,1) and z in states|{halt}
    todo=[0];seen=set()
    while todo:
        q=todo.pop()
        if q in seen or q==halt:continue
        seen.add(q);todo.extend(t[q,b][2] for b in (0,1))
    assert seen==states

def local_trace(t,start,initial,steps,target,head):
    """Read only explicitly known cells; all others stay arbitrary and unread."""
    cells=dict(initial);p=0;s=start;trace=[]
    for k in range(steps):
        assert p in cells, ('Read unspecified exterior',s,p)
        bit=cells[p];w,d,z=t[s,bit]
        trace.append([s,p,bit,w,d,z]);cells[p]=w;p+=d;s=z
    assert (s,p)==(target,head)
    assert cells==initial,'Local macro changed tape'
    return trace

def check_guards(t,compatibility=False):
    expected={
      172:[(116,0,0,1)],
      116:[(215,1,1,1)],
      211:[(163,0,0,-1),(163,1,1,1)],
      163:[(132,1,1,1),(199,1,1,1),(217,0,0,1)],
      217:[(216,1,1,1)]}
    if compatibility:
        expected={172:[(116,0,0,1)],116:[(163,1,1,1)],
          211:[(216,0,0,-1),(216,1,1,1)],
          216:[(132,1,1,1),(199,1,1,1),(214,0,0,1)],
          214:[(217,1,1,1)]}
    for q,census in expected.items():assert incoming(t,q)==census
    return expected

def check_history(t):
    """Independent exhaustive 3-step guard audit, plus shorter start prefixes."""
    def step(front):
        out=set()
        for q,items in front:
            if q==254:continue
            cells=dict(items)
            for b in ([cells[0]] if 0 in cells else [0,1]):
                w,d,z=t[q,b]
                nxt={x-d:v for x,v in cells.items()};nxt[-d]=w
                out.add((z,tuple(sorted(nxt.items()))))
        return out
    frontier={(q,()) for q,b in t};early={(0,())};start=early.copy()
    for _ in range(3):
        frontier=step(frontier);start=step(start);early.update(start)
    checked=[]
    for q,items in sorted(frontier|early):
        c=dict(items)
        if q==172:
            assert c.get(-2)==1 and c.get(-1)==0
            checked.append([q,dict(items)])
        if q==211:
            assert c.get(0)==1 or c.get(-1)==1
            checked.append([q,dict(items)])
    assert any(q==172 for q,c in checked) and any(q==211 for q,c in checked)
    return checked

def build(parent,output,compatibility=False):
    parent_sha=COMPAT_SHA if compatibility else PARENT_SHA
    helper=214 if compatibility else 217
    raw=Path(parent).read_bytes();assert hashlib.sha256(raw).hexdigest()==parent_sha
    old=read(parent);check_census(old,209,254)
    guards=check_guards(old,compatibility);histories=check_history(old)
    assert old[172,0]==(0,-1,67) and old[172,1]==(1,1,184)
    assert old[211,0]==(0,1,157) and old[211,1]==(1,1,184)
    new={(q,b):(w,d,211 if z==172 else z) for (q,b),(w,d,z) in old.items() if q!=172}
    new[211,0]=(0,-1,helper)
    check_census(new,208,254)
    cases=[
      dict(old_state=172,read=0,guard={-2:1,-1:0,0:0},steps=7,target=67,head=-1),
      dict(old_state=172,read=1,guard={-2:1,-1:0,0:1},steps=1,target=184,head=1),
      dict(old_state=211,read=0,guard={-1:1,0:0},steps=3,target=157,head=1),
      dict(old_state=211,read=1,guard={0:1},steps=1,target=184,head=1)]
    for c in cases:
        ow,od,oz=old[c['old_state'],c['read']]
        assert (ow,od,oz)==(c['read'],c['head'],c['target'])
        c['trace']=local_trace(new,211,c['guard'],c['steps'],c['target'],c['head'])
    ordinary=0
    for (q,b),(w,d,z) in old.items():
        if q not in (172,211):
            assert new[q,b]==(w,d,211 if z==172 else z);ordinary+=1
    assert ordinary==414
    mapping={q:i for i,q in enumerate(sorted({q for q,b in new}))};mapping[254]=208
    dense={(mapping[q],b):(w,d,mapping[z]) for (q,b),(w,d,z) in new.items()}
    check_census(dense,208,208)
    output=Path(output);output.mkdir(parents=True,exist_ok=True)
    payload={'u208.native.tm':encode(new),'u208.tm':encode(dense),'state_map.json':json.dumps(mapping,indent=2)+'\n'}
    for name,content in payload.items():(output/name).write_text(content)
    cert={'status':'PASS','working_states':208,'transition_rows':416,'parent_sha256':parent_sha,
      'removed':172,'representative':211,'changed_row':[211,0,0,-1,helper],
      'ordinary_quotient_rows':ordinary,'incoming_censuses':guards,'history_contexts':histories,
      'cases':cases,'hashes':{k:hashlib.sha256(v.encode()).hexdigest() for k,v in payload.items()},
      'scope':'All-tape halting equivalence from state 0, by positive-block exact simulation; no assertion of PA consistency.'}
    (output/'local_certificate.json').write_text(json.dumps(cert,indent=2)+'\n')
    print(json.dumps({k:v for k,v in cert.items() if k not in ('incoming_censuses','history_contexts','cases')},indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('parent');p.add_argument('--output',required=True);p.add_argument('--compatibility',action='store_true');a=p.parse_args();build(a.parent,a.output,a.compatibility)

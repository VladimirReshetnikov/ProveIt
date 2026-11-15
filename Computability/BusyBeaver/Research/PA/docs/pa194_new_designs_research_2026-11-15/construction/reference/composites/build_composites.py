#!/usr/bin/env python3
"""Combine one incoming history selector with the two exact accelerations.

Parent AX11H and LC_AX11H tables are pinned in parents/. The independent
literal checker and written proof in this packet supply the preservation
argument; reconstruction alone is not evidence of semantic correctness.
"""
from pathlib import Path
import json,hashlib
D=Path(__file__).resolve().parent
PARENT_SHA={'AX11H':'6022711dcc0a025eb4b7a5a8f690d6b52f45f3d963a0868afef10962ccc49bd3','LC_AX11H':'e7800298659a5768a8aabfbd0cfd0ea42af241ed2a10b0cc1dbf64ed8aff1112'}
PAIRS=[(127,124,8,59)]
PATCH={(26,1):(1,'R',91),(101,0):(0,'R',17)}
def read(p):
 rows={}
 for l in p.read_text().splitlines():
  if not l.strip() or l.lstrip().startswith('#'):continue
  q,b,w,d,n=l.split();rows[int(q),int(b)]=(int(w),d,int(n))
 return rows

def text(t):return ''.join(f'{q} {b} {w} {d} {n}\n' for (q,b),(w,d,n) in sorted(t.items()))
def dense(t):
 labels=[74]; ix={74:0}
 for q in labels:
  for b in(0,1):
   n=t[q,b][2]
   if n!=254 and n not in ix:ix[n]=len(labels);labels.append(n)
 assert len(labels)==194 and set(labels)=={q for q,b in t}
 ix[254]=194
 return {(ix[q],b):(w,d,ix[n]) for(q,b),(w,d,n)in t.items()},labels+[254]
for name in['AX11H','LC_AX11H']:
 assert hashlib.sha256((D/'parents'/f'{name}.native.tm').read_bytes()).hexdigest()==PARENT_SHA[name]
 old=read(D/'parents'/f'{name}.native.tm')
 f=lambda q:{r:l for l,r,u,v in PAIRS}.get(q,q)
 selector={(q,b):(w,d,f(n))for(q,b),(w,d,n)in old.items()}
 for l,r,u,v in PAIRS:
  selector[l,0]=(0,'L',r);selector[r,0]=(0,'R',u);selector[r,1]=(1,'R',v)
 child=dict(selector);child.update(PATCH)
 table,labels=dense(child)
 out=D/'machines'/('PA194'+name+'_SF');out.mkdir(parents=True,exist_ok=True)
 for fname,t in [('selector.native.tm',selector),('machine.native.tm',child),('machine.tm',table)]:
  (out/fname).write_text(text(t))
 (out/'labels.json').write_text(json.dumps(labels)+'\n')
 changes=[{'state':q,'read':b,'parent':list(old[q,b]),'child':list(child[q,b])}for q,b in sorted(old)if old[q,b]!=child[q,b]]
 record={'name':out.name,'parent':name,'parent_native_sha256':hashlib.sha256((D/'parents'/f'{name}.native.tm').read_bytes()).hexdigest(),'machine_sha256':hashlib.sha256((out/'machine.tm').read_bytes()).hexdigest(),'native_sha256':hashlib.sha256((out/'machine.native.tm').read_bytes()).hexdigest(),'states':194,'rows':388,'dense_start':0,'dense_halt':194,'native_start':74,'native_halt':254,'edits':changes,'selectors':PAIRS,'fast_edits':[[*k,*v]for k,v in PATCH.items()],'proof_claim':'Direct relative iPRA equivalence to the pinned parent; absolute calibration is inherited separately.'}
 (out/'construction.json').write_text(json.dumps(record,indent=2)+'\n');print(out.name,record['machine_sha256'],len(changes))

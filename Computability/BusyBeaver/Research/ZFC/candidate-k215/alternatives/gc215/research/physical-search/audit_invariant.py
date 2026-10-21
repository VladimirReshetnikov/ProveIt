#!/usr/bin/env python3
"""Independent replay of finite window invariant closure, with no worklist search."""
from pathlib import Path
import json,hashlib,argparse

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def audit(table_path,proof_path):
 table={};start=0
 for line in table_path.read_text().splitlines():
  if line.startswith('#! start '):start=int(line[9:])
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();key=(int(q),int(b));assert key not in table;table[key]=(int(w),-1 if d=='L' else 1,int(z));assert d in ('L','R')
 data=json.loads(proof_path.read_text());r=data['radius'];width=2*r+1;domain=1<<width
 inv={int(q):set(ms) for q,ms in data['masks'].items()};assert set(inv)=={q for q,b in table};assert all(0<=m<domain for ms in inv.values() for m in ms)
 assert inv[start]>=({0}if data['blank_window']else set(range(domain)))
 tested=0
 for q,ms in inv.items():
  for old in ms:
   b=(old>>r)&1;write,dest_shift,nextq=table[q,b]
   if nextq not in inv:continue
   # Read a concrete list ordered from leftmost to rightmost window cell.
   bits=[(old>>j)&1 for j in range(width)];bits[r]=write
   for exterior in (0,1):
    moved=(bits[1:]+[exterior])if dest_shift==1 else([exterior]+bits[:-1])
    nxt=sum(x<<j for j,x in enumerate(moved));assert nxt in inv[nextq],(q,old,nextq,nxt)
    tested+=1
 local={q:{((m>>(r-1))&7) for m in ms}for q,ms in inv.items()}
 assert local=={int(q):set(ms)for q,ms in data['local'].items()}
 pairs=data['distinguishable_pairs']
 for a in pairs:
  p,q,b,side=a['p'],a['q'],a['branch'],a['side'];k=r+side
  assert table[p,1-b]==table[q,1-b]
  assert {(m>>k)&1 for m in inv[p]if((m>>r)&1)==b}=={a['pmarker']}
  assert {(m>>k)&1 for m in inv[q]if((m>>r)&1)==b}=={a['qmarker']}
  assert a['pmarker']!=a['qmarker'];assert list(table[p,b])==a['ptransition']and list(table[q,b])==a['qtransition']
 return dict(status='INDEPENDENT_INDUCTIVE_CLOSURE_PASS',radius=r,blank_window_only=data['blank_window'],configurations=sum(map(len,inv.values())),tested_successors=tested,conditional_pairs=len(pairs),table_sha256=sha(table_path),invariant_sha256=sha(proof_path),scope='Exact finite inductive closure including both outside bits. Therefore covers every actual configuration from the declared initial-window domain, regardless of tape outside it. This is ordinary finite arithmetic evidence, not a proof-assistant kernel theorem.')
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('table',type=Path);p.add_argument('invariant',type=Path);p.add_argument('--output',type=Path);a=p.parse_args();out=audit(a.table,a.invariant);raw=json.dumps(out,indent=2)+'\n';print(raw,end='');a.output.write_text(raw) if a.output else None

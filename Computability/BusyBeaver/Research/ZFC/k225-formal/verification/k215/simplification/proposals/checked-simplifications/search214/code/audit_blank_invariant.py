#!/usr/bin/env python3
"""Independently audit a blank-seeded finite-window invariant.
Uses explicit lists of Boolean cells rather than the generator's bit shifts.
"""
from pathlib import Path
import argparse,hashlib,json

def need(ok,msg):
 if not ok: raise ValueError(msg)
def parse(path):
 T={};start=None
 for line in Path(path).read_text().splitlines():
  if line.startswith('#! start '):start=int(line[9:])
  if not line or line.startswith('#'):continue
  q,b,w,d,t=line.split();key=(int(q),int(b));need(key not in T,'duplicate row');T[key]=(int(w),d,int(t))
 need(start is not None,'missing start');return T,start

def audit(table,certificate):
 T,start=parse(table);x=json.loads(Path(certificate).read_text());r=x['radius'];need(r>=1 and r<=10,'radius domain');W=2*r+1
 states={q for q,b in T};need({b for q,b in T}=={0,1},'binary domain');need(all((q,b)in T for q in states for b in [0,1]),'totality')
 masks={int(q):set(ms) for q,ms in x['masks'].items()};need(set(masks)==states,'control census');need(x['blank_window'] is True,'blank start premise');need(0 in masks[start],'initial blank window')
 need(all(len(ms)==len(x['masks'][str(q)]) for q,ms in masks.items()),'duplicate mask');need(all(0<=v<2**W for ms in masks.values() for v in ms),'mask domain')
 need(sum(map(len,masks.values()))==x['configs'],'configuration census');edges=0;halt_edges=0
 for q,ms in masks.items():
  for m in ms:
   bits=[(m//(2**i))%2 for i in range(W)];b=bits[r];w,d,t=T[q,b];need(w in [0,1] and d in ['L','R'],'transition domain');bits[r]=w
   if t not in states:
    need(t==254,'unexpected halt');halt_edges+=1;continue
   for exterior in [0,1]:
    moved=bits[1:]+[exterior] if d=='R' else [exterior]+bits[:-1]
    encoded=sum(v*2**i for i,v in enumerate(moved));need(encoded in masks[t],f'closure failure {q} {m}');edges+=1
 for p in x['distinguishable_pairs']:
  a,b,branch,side=p['p'],p['q'],p['branch'],p['side'];need(side in [-1,1] and branch in [0,1],'pair domain');need(T[a,1-branch]==T[b,1-branch],'common branch')
  for q,marker in [(a,p['pmarker']),(b,p['qmarker'])]:
   selected=[m for m in masks[q] if (m//2**r)%2==branch];need(selected,'empty origin domain');need(all((m//2**(r+side))%2==marker for m in selected),'marker premise')
  need(p['pmarker']!=p['qmarker'],'distinct origin marker')
 absent=[[q,b] for q in sorted(states) for b in [0,1] if not any((m//2**r)%2==b for m in masks[q])];need(absent==x['unreachable_rows'],'absent rows')
 return dict(status='PASS',radius=r,configurations=x['configs'],successor_obligations=edges,halt_contexts=halt_edges,conditional_pairs=len(x['distinguishable_pairs']),absent_rows=absent,table_sha256=hashlib.sha256(Path(table).read_bytes()).hexdigest(),invariant_sha256=hashlib.sha256(Path(certificate).read_bytes()).hexdigest())
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('table');p.add_argument('invariant');p.add_argument('--out');a=p.parse_args();res=audit(a.table,a.invariant);s=json.dumps(res,indent=2)+'\n';print(s,end='');
 if a.out:Path(a.out).write_text(s)

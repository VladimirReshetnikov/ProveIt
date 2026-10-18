#!/usr/bin/env python3
"""Independent literal replay of a synthesized return-run detector.

The nine inputs are complete symbolic cylinder sets: unknown exterior tape
is never inspected, and every known cell is restored. Replaying the finite
interior trace therefore proves each accepted local contract for arbitrary
exterior extensions, by induction on that trace. The long input requires only
the recorded known zero window; an exit outside it stops before the next read.
"""
from pathlib import Path
import argparse,json,hashlib

def check_model(path):
 record=json.loads(path.read_text());assert record['status']=='sat'
 n=record['states'];fuel=record['step_bound'];table={}
 long_min_read=record.get('long_min_read',-16)
 long_min_exit=record.get('long_min_exit')
 long_exit_head=record.get('long_exit_head')
 for q,b,w,d,t in record['table']:
  assert q in range(n)and b in(0,1)and w in(0,1)and d in('L','R')and t in range(n+2)
  assert(q,b)not in table;table[q,b]=(w,-1 if d=='L' else 1,t)
 assert set(table)=={(q,b)for q in range(n)for b in(0,1)}
 checks=[]
 for k in range(9):
  short=k<8;known_left=-k if short else long_min_read
  initial={2}|({-k}if short else set())
  one=set(initial);q=0;h=0;trace=[]
  for tick in range(fuel):
   if q>=n:break
   assert known_left<=h<=2,('unknown exterior read',k,tick,q,h)
   b=int(h in one);w,d,t=table[q,b]
   trace.append(dict(state=q,head=h,read=b,write=w,move=d,next=t))
   if w:one.add(h)
   else:one.discard(h)
   h+=d;q=t
  assert one==initial,('unrestored tape',k,q,h,sorted(one),sorted(initial))
  if short:assert(q,h)==(n,-k-1),(k,q,h)
  else:
   assert q==n+1 and h<=1,(k,q,h)
   if long_min_exit is not None:assert h>=long_min_exit,(k,q,h)
   if long_exit_head is not None:assert h==long_exit_head,(k,q,h)
  assert trace and len(trace)<=fuel
  # If the long exit is inside the known zero word, unchanged 84 scans to 2.
  # An exact exit at -8 may instead stop before reading opaque exterior.
  finish=dict(state=4,head=h)if short else (dict(state=96,head=3)if h>=known_left else dict(state=84,head=h,continuation_depends_on_unknown_exterior=True))
  checks.append(dict(first_left_one=(-k if short else None),short=short,
   steps=len(trace),exit='4'if short else'84',exit_head=h,
   final_after_84=finish,read_min=min(s['head']for s in trace),
   read_max=max(s['head']for s in trace),trace=trace))
 return dict(status='PASS',model_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
  states=n,source_step_bound=fuel,contracts=9,
  proof_scope='Finite exact traces with no reads outside their known word; arbitrary exterior transport follows by literal induction. The local proof stops at the stated exit before any further read.',
  checks=checks)

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('model',type=Path);ap.add_argument('--output',type=Path);a=ap.parse_args()
 r=check_model(a.model);out=a.output or Path(__file__).with_name('detector-replay-'+a.model.stem+'.json');out.write_text(json.dumps(r,indent=2)+'\n')
 print(json.dumps({k:v for k,v in r.items()if k!='checks'},indent=2));print('durations',[c['steps']for c in r['checks']]);print('wrote',out)
if __name__=='__main__':main()

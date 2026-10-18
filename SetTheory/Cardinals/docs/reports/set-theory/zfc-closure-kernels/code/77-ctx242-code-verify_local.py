#!/usr/bin/env python3
"""Reconstruct and verify the contextual return fold from combined243.

This checker is a finite premise checker for the ordinary induction proof,
not a proof-assistant kernel. It also performs a separate exact blank prefix
comparison. The local checks have arbitrary exterior tapes: each block only
reads/writes the supplied finite cells; equality of their finite dictionaries
therefore implies equality of complete arbitrary binary tapes.
"""
from __future__ import annotations
from pathlib import Path
from collections import Counter
import hashlib,json,itertools,argparse
OLD_SHA='4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300'
ROOT=Path(__file__).resolve().parents[1]
DEFAULT=ROOT/'reference/combined243/zfc_combined243_old.tm'
PATCH={(15,0):(0,'L',32),(18,0):(0,'L',15),(47,0):(0,'L',15),(65,0):(0,'L',15)}
I_STATES={15,18,47,65}

def read(path):
 t={}
 for l in path.read_text().splitlines():
  if not l or l.startswith('#'):continue
  q,b,w,d,r=l.split();key=(int(q),int(b));assert key not in t
  t[key]=(int(w),d,int(r))
 return t

def encode(t,start=95):
 return '#! start '+str(start)+'\n'+''.join(f'{q} {b} {w} {d} {r}\n' for (q,b),(w,d,r) in sorted(t.items()))

def run_exact(t,q,h,tape,n):
 tape=dict(tape);used=[]
 for _ in range(n):
  assert h in tape, ('unprovided_exterior_read',q,h)
  b=tape[h];w,d,q2=t[q,b];used.append((q,b));tape[h]=w
  h+=1 if d=='R' else -1;q=q2
 return (q,h,tape),used

def blank_prefix(t,limit,stop=None):
 q=95;h=0;ones=set();counts=Counter()
 for tick in range(limit+1):
  if stop is not None and (q,h,ones)==stop:return (q,h,ones),tick,counts
  if tick==limit:break
  assert q!=254,('early_halt',tick)
  key=q,int(h in ones);counts[key]+=1;w,d,q=t[key]
  if w:ones.add(h)
  else:ones.discard(h)
  h+=1 if d=='R' else -1
 return (q,h,ones),tick,counts

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--old',type=Path,default=DEFAULT);ap.add_argument('--out',type=Path,default=ROOT/'evidence/local-reproduction');args=ap.parse_args()
 assert __debug__;assert hashlib.sha256(args.old.read_bytes()).hexdigest()==OLD_SHA
 old=read(args.old);assert len(old)==486 and len({q for q,b in old})==243
 new={k:v for k,v in old.items() if k[0]!=27};new.update(PATCH)
 assert len(new)==484 and len({q for q,b in new})==242
 assert all(r!=27 for w,d,r in new.values())
 assert {(q,b) for q,b in old if old[q,b][2]==27}=={(18,0),(47,0),(65,0)}
 assert old[27,0]==(0,'L',32)
 incoming={q:[(key,act) for key,act in old.items() if act[2]==q] for q in I_STATES}
 assert all(w==0 and d=='R' for rows in incoming.values() for key,(w,d,q) in rows)
 assert 95 not in I_STATES
 assert old[15,0]==(0,'R',21)
 assert new[32,0]==old[32,0]==(0,'R',45)
 assert new[45,0]==old[45,0]==(0,'R',21)
 changed={k for k in new if old[k]!=new[k]};assert changed==set(PATCH)
 # Exhaustive local words over -2,-1,0,+1; the relevant guards imply -1=0.
 records=[]
 for q in (15,18,47,65):
  for left2,right1 in itertools.product((0,1),repeat=2):
   tape={-2:left2,-1:0,0:0,1:right1}
   m,n=(1,3) if q==15 else (2,2)
   a,ua=run_exact(old,q,0,tape,m);b,ub=run_exact(new,q,0,tape,n)
   assert a==b and a[0] not in (27,254)
   records.append({'entry':q,'word':tape,'old_steps':m,'new_steps':n,'endpoint_state':a[0],'endpoint_head':a[1],'old_rows':ua,'new_rows':ub})
 # All other retained rows agree and do not go to deleted27.
 ordinary=[k for k in new if k not in changed]
 assert len(ordinary)==480
 assert all(new[k]==old[k] and old[k][2]!=27 for k in ordinary)
 args.out.mkdir(parents=True,exist_ok=True)
 inherited=args.out/'zfc_return_fold242_old.tm';inherited.write_text(encode(new))
 order=[95]+sorted({q for q,b in new}-{95});ren={q:i for i,q in enumerate(order)};ren[254]=242
 canon={(ren[q],b):(w,d,ren[r]) for (q,b),(w,d,r) in new.items()}
 canonical=args.out/'zfc_return_fold242.tm';canonical.write_text(encode(canon,0))
 (args.out/'renumbering.json').write_text(json.dumps({'old_to_new':ren,'new_to_old':{v:k for k,v in ren.items()}},indent=2)+'\n')
 target,old_ticks,old_counts=blank_prefix(old,407967)
 assert target[0]==96 and target[1]==-5 and len(target[2])==351
 got,ticks,new_counts=blank_prefix(new,old_ticks+100000,stop=target)
 assert got==target
 assert ticks==old_ticks+2*old_counts[15,0]
 evidence={'status':'pass','source_sha256':OLD_SHA,'inherited_sha256':hashlib.sha256(inherited.read_bytes()).hexdigest(),'canonical_sha256':hashlib.sha256(canonical.read_bytes()).hexdigest(),'working_states':242,'rows':484,'changed_rows':[{'row':k,'old':old[k],'new':new[k]} for k in sorted(changed)],'deleted':27,'invariant_states':sorted(I_STATES),'invariant_incoming':{str(k):v for k,v in incoming.items()},'ordinary_rows':len(ordinary),'local_blocks':records,'blank_prefix':{'old_steps':old_ticks,'new_steps':ticks,'old15_read0_visits':old_counts[15,0],'head':target[1],'state':target[0],'ones':sorted(target[2]),'one_count':len(target[2])},'scope':'Finite premise check for universal positive-block ordinary proof plus separate exact blank execution; no proof-assistant kernel claim.'}
 (args.out/'verification.json').write_text(json.dumps(evidence,indent=2)+'\n')
 print(json.dumps({k:evidence[k] for k in ('status','working_states','rows','inherited_sha256','canonical_sha256')}))
 print(json.dumps({k:evidence['blank_prefix'][k] for k in ('old_steps','new_steps','old15_read0_visits','head','state','one_count')}))
if __name__=='__main__':main()

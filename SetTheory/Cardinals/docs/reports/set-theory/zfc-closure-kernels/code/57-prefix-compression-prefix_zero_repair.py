#!/usr/bin/env python3
"""Sample synthesis for sharing positive and zero decrement left scanners."""
from pathlib import Path
import sys,json,time
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'redesign'))
import prefix_decrement as p
p.generate();audit=p.m.audit
T=audit.read_table((ROOT/'compression/prefix_zero250.tm').read_bytes())
base=p.generate()
def inputs():
 selected={}
 for pc,op,r in p.m.a.sites:
  if op=='CD':selected.setdefault(p.PERM[r],pc)
 for r,pc in sorted(selected.items()):
  for regs in ([0]*9,[i%3 for i in range(9)],[5,0,1,0,2,0,3,0,4]):
   regs=list(regs);regs[r]=0
   for gap,spares in ((43,[]),(45,[0]*2),(44,[2,0,1])):
    q,h,ones=96,0,audit.paint(pc,gap,regs,spares,0)
    for step in range(5000):
     if q==0 and h not in ones:break
     w,d,q=base[q,int(h in ones)]
     if w:ones.add(h)
     else:ones.discard(h)
     h+=1 if d=='R' else -1
    else:raise AssertionError(('restore entry not reached',pc,r))
    nxt=audit.successor(pc,'CD',r,True);outhead=-(nxt is None)
    targets=[audit.paint(''if nxt is None else nxt,gap+(nxt is None)+extra,regs,spares,outhead)for extra in range(3)]
    yield dict(pc=pc,r=r,registers=regs,gap=gap,spares=spares,head=h,ones=ones,outhead=outhead,targets=targets)
def run(table,case,fuel=5000):
 q,h,ones=0,case['head'],case['ones'].copy()
 for step in range(fuel):
  if q==96 and h==case['outhead']:
   for extra,target in enumerate(case['targets']):
    if ones==target:return dict(passed=True,steps=step,growth=extra)
  if q==254 or (q,int(h in ones))not in table:return dict(passed=False,reason='halt_or_missing',steps=step)
  w,d,q=table[q,int(h in ones)]
  if w:ones.add(h)
  else:ones.discard(h)
  h+=1 if d=='R'else-1
 return dict(passed=False,reason='fuel',steps=fuel)
def main():
 begun=time.monotonic();cases=list(inputs());states=sorted({q for q,b in T})+[254];tested=0;survivors=[];near=[]
 for w in range(2):
  for d in ('L','R'):
   for target in states:
    table=T.copy();table[0,0]=w,d,target;tested+=1
    for i,case in enumerate(cases):
     outcome=run(table,case)
     if not outcome['passed']:break
    else:
     stem=f'prefix_zero250_repair_{w}{d}{target}.tm';(ROOT/'compression'/stem).write_bytes(audit.encode(table));survivors.append(stem)
     print('SURVIVOR',stem,flush=True);continue
    if i>0:
     near.append(dict(action=[w,d,target],cases_passed=i,failure={k:v for k,v in case.items()if k not in('ones','targets')},outcome=outcome))
 result=dict(scope=__doc__,cases=len(cases),tested=tested,survivors=survivors,near=near,seconds=time.monotonic()-begun)
 (ROOT/'compression/prefix_zero_repair.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()

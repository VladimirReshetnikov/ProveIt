#!/usr/bin/env python3
from predecessor_multiblock import *
from itertools import product

def scan(t,ctx,R,steps=64):
 incoming=defaultdict(list)
 for k,(_,_,v) in t.items():
  if k[0]!=v:incoming[v].append(k)
 candidates=[(drop,prev) for drop,prev in incoming.items() if drop not in (0,196)]
 out=[];count=0;row_survivors=[]
 for drop,parents in sorted(candidates):
  choices={}
  for qp,bp in parents:
   cases=[(a,old_goals(t,drop,qp,bp,a,R,steps)) for a in ctx[qp,bp]]
   opts=[]
   for n in range(197):
    if n==drop:continue
    for d in (-1,1):
     for w in (0,1):
      patch=w,d,n;count+=1;ks=[]
      for a,goal in cases:
       k=check(t,drop,qp,bp,patch,a,goal,R,steps)
       if k is None:break
       ks.append(k)
      else:
       if cases:opts.append({'patch':[w,'R' if d==1 else'L',n],'lengths':sorted(set(ks)),'cases':len(cases)})
   if opts:
    choices[qp,bp]=opts
    row_survivors.append({'drop':drop,'parent_row':[qp,bp],'choices':opts})
   else:break
  if len(choices)==len(parents):
   result={'drop':drop,'choices':[{'row':list(k),'patches':v}for k,v in choices.items()]}
   out.append(result);print('SURVIVOR',result,flush=True)
  print('done',drop,'parents',len(parents),'completed',len(choices),'patches',count,flush=True)
 return out,candidates,count,row_survivors

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--radius',type=int,default=6);ap.add_argument('--steps',type=int,default=64);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 start=time.monotonic();t=read(P);ctx,N=closure(t,a.radius);print('closure',N,flush=True)
 out,cases,count,row_survivors=scan(t,ctx,a.radius,a.steps)
 receipt={'source_sha256':hashlib.sha256(P.read_bytes()).hexdigest(),'template':'all incoming rows replaced, arbitrary old block beyond deleted state','radius':a.radius,'max_steps':a.steps,'closure_configurations':N,'drop_candidates':len(cases),'tested_patches':count,'survivors':out,'row_survivors':row_survivors,'elapsed_seconds':time.monotonic()-start}
 a.output.write_text(json.dumps(receipt,indent=2)+'\n');print(receipt)
if __name__=='__main__':main()

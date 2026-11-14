import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'verification'))
from layout import *
from words import initial,encode
from pathlib import Path
import time,random,math
BASE=Path(__file__).resolve().parent
oldmachine=machine
MACROS['noop6']=108

# Fresh parser with explicit provenance of new no-op occurrences.
def source_noop(t):
 nodes=raw_nodes();nodes['noop6']=nodes['node0'];sites=[];noops=set();unreachable=set()
 def walk(t,p):
  if isinstance(t,str):
   if t=='x67':return walk(ax,p)
   if t=='noop6':
    noops.add(len(sites));unreachable.add(len(sites)+1)
   return walk(nodes[t],p)
  if t[0]=='leaf':sites.append((p,t[1],t[2]));return
  walk(t[0],p+(0,));walk(t[1],p+(1,))
 ax=t;walk('node172',())
 def locate(p):
  for i,(q,_,_)in enumerate(sites):
   if q[:len(p)]==p or(p[:len(q)]==q and not any(p[len(q):])):return i
  raise ValueError(p)
 def after(p):
  for i in range(len(p)-1,-1,-1):
   if p[i]==0:return locate(p[:i]+(1,))
  raise ValueError(('exit',p))
 def cut(p,b,k):
  for i in range(len(p)-1,-1,-1):
   if p[i]==b:
    k-=1
    if not k:return p[:i]
  raise ValueError((p,b,k))
 ins=[]
 for p,op,arg in sites:
  if op=='inc':x=('inc',arg,after(p))
  elif op=='dec':x=('dec',arg,after(cut(p,0,1)),after(p))
  elif op=='breakTo':x=('jump',after(cut(p,0,arg)))
  elif op=='continueTo':x=('jump',locate(cut(p,1,arg)))
  elif op=='halt':x=('halt',)
  else:raise ValueError(op)
  ins.append(x)
 cs=[]
 for i,code in enumerate(ins):
  if i in unreachable:continue
  st=frame(sites[i][0])
  if code[0]=='inc':
   _,r,n=code;cs.append((i,None,st,canonical(frame(sites[n][0],0,('x','inc',PHYSICAL[r])))))
  elif code[0]=='dec':
   _,r,z,p=code;cs.append((i,(PHYSICAL[r],True),st,canonical(frame(sites[z][0]))))
   if i not in noops:cs.append((i,(PHYSICAL[r],False),st,canonical(frame(sites[p][0],1,('x','dec',PHYSICAL[r])))))
  elif code[0]=='jump':cs.append((i,None,st,canonical(frame(sites[code[1]][0]))))
  else:cs.append((i,None,st,None))
 return sites,ins,cs,noops,unreachable

def wrap(t,target,side):
 if t==target:return ('noop6',t)if side==0 else(t,'noop6')
 if isnode(t):return wrap(t[0],target,side),wrap(t[1],target,side)
 return t

def apply_folds(r,ops,match):
 choices=[]
 for a,b in match:
  oo=next(o for x,y,o in ops if(x,y)==(a,b))
  choices.append([(a,b,(x,y))for x,y in itertools.product(*oo)])
 for selected in itertools.product(*choices):
  alias={a:b for a,b,acts in selected};actions={b:acts for a,b,acts in selected};rr={}
  for(q,bit),act in r.items():
   if q in alias:continue
   w,d,n=actions[q][bit]if q in actions else act
   rr[q,bit]=w,d,alias.get(n,n)
  yield rr,selected

def inspect(t,meta):
 r,index,sh=build(t);ops=opportunities_fast(r,sh);match=max_matching(ops);cost=len(r)//2-len(match)
 print('candidate',meta,'raw',len(r)//2,'folds',len(match),'effective',cost,flush=True)
 if cost<=196:
  sites,ins,cs,no,un=source_noop(t)
  base=validate(r,cs);print('raw_validation',base,flush=True)
  if base['ok']:
   for rr,selected in apply_folds(r,ops,match):
    ans=validate(rr,cs)
    if ans['ok']:
     print('VERIFIED',meta,len(rr)//2,ans,flush=True)
     out={'grammar':encode(t),'meta':meta,'rows':[[q,b,*a]for(q,b),a in sorted(rr.items())],'folds':selected,'source_sites':sites,'instructions':ins,'noop_zero_sites':sorted(no),'unreachable_sites':sorted(un),'validation':ans}
     Path(f'noop_{len(rr)//2}_{str(meta).replace(" ","")}.json').write_text(json.dumps(out,indent=2))
     if len(rr)//2<196:return out
 return None
if __name__=='__main__':
 targets=list(MACROS);targets.remove('noop6');targets=[m for m in targets if m not in ['node142','node150']]
 for target in targets:
  for side in (0,1):
   if inspect(wrap(initial,target,side),(str(target),side)):raise SystemExit()

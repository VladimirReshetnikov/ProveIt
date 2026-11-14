"""Exhaustive exact two-cell one-helper folds with globally forced entry tag."""
import sys,json,itertools
from pathlib import Path
from collections import defaultdict
H=Path(__file__).resolve().parent;sys.path.insert(0,str(H));from transplant import read,encode

def opportunities(T,start=0):
 states={q for q,b in T};incoming=defaultdict(set);left=set()
 for(q,b),(w,d,n)in T.items():
  if d==1:incoming[n].add(w)
  else:left.add(n)
 tag0=[q for q in states if incoming[q]=={0}and q not in left and q!=start]
 tag1=[q for q in states if incoming[q]=={1}and q not in left and q!=start]
 providers=[defaultdict(list),defaultdict(list)]
 for h in states:
  w0,d0,u0=T[h,0];w1,d1,u1=T[h,1]
  if(w0,d0,w1,d1)!=(0,1,1,1):continue
  for b in(0,1):
   if(u0,b)in T and(u1,b)in T:providers[b][T[u0,b],T[u1,b]].append((h,u0,u1))
 out=[]
 for a in tag0:
  for b in tag1:
   opts=[]
   for bit in(0,1):
    A,B=T[a,bit],T[b,bit]
    if A==B:opts.append([A]);continue
    opts.append([(bit,-1,h)for h,u0,u1 in providers[bit].get((A,B),[])if not{a,b}&{h,u0,u1}])
   if all(opts):out.append((a,b,opts))
 return out

def fold(T,a,b,acts):
 return{(q,c):(w,d,b if n==a else n)for(q,c),act in T.items()if q!=a for w,d,n in[acts[c]if q==b else act]}

def local(T,V,a,b):
 def pi(q):return b if q==a else q
 for q,tag in[(a,0),(b,1)]:
  for bit in(0,1):
   w,d,n=T[q,bit];goal=({-1:tag,0:w},d,pi(n));tape={-1:tag,0:bit};head=0;state=b
   for k in range(1,30):
    assert head in tape,(q,bit,k,head)
    w2,d2,n2=V[state,tape[head]];tape[head]=w2;head+=d2;state=n2
    if(tape,head,state)==goal:break
   else:raise ValueError('no match')
 return True

T=read(H/'hybrid196.native.tm');allresults=[];neutral_results=[]
ops=opportunities(T);base_count=len(ops);print('BASE FOLDS',len(ops),ops[:5],flush=True)
for i,(a,b,opts)in enumerate(ops):
 V=fold(T,a,b,[x[0]for x in opts]);local(T,V,a,b);out=H/'local195';out.mkdir(exist_ok=True);(out/f'base_{i}.tm').write_text(encode(V));allresults.append({'kind':'direct','drop':a,'keep':b,'opts':opts})
# Apply each known neutral U208 helper arrangement that transports globally.
manifest=H.parent/'comparison/inputs/manifest.json'
if not manifest.exists():manifest=H.parents[1]/'incoming_extracted/pa_tm_comparison_and_reductions/pa_tm_research/comparison/inputs/manifest.json'
m=json.loads(manifest.read_text())
U=read(H/'u208.native.tm')
for r in m['helper_recipes']:
 if r['baseline']!='A':continue
 a,b,bit,x0,x1,w0,w1=r['parameters']
 if not all(T.get((q,z))==U[q,z]for q in(a,b)for z in(0,1)):continue
 incoming={q:[(w,d)for(k,c),(w,d,n)in T.items()if n==q]for q in(a,b)}
 if any(not inc or any(d!=1 for w,d in inc)or len({w for w,d in inc})!=1 for inc in incoming.values()):continue
 V={(q,c):(w,d,b if n==a else n)for(q,c),(w,d,n)in T.items()if q!=a}
 V[b,bit]=(bit,-1,500);V[500,0]=(w0,1,b if x0==a else x0);V[500,1]=(w1,1,b if x1==a else x1)
 # Verify recipe with its actual entry tags, which need not be a=0,b=1.
 def pi(q):return b if q==a else q
 for q in(a,b):
  tag=incoming[q][0][0]
  for readbit in(0,1):
   w,d,n=T[q,readbit];goal=({-1:tag,0:w},d,pi(n));tape={-1:tag,0:readbit};head=0;state=b
   for k in range(1,30):
    assert head in tape
    w2,d2,n2=V[state,tape[head]];tape[head]=w2;head+=d2;state=n2
    if(tape,head,state)==goal:break
   else:raise ValueError('recipe fails')
 ops=opportunities(V);neutral_results.append({'id':r['id'],'states':len(V)//2,'incoming_tags':{q:sorted(set(w for w,d in incoming[q]))for q in(a,b)},'local_step_obligations_passed':4,'fold_count':len(ops)});print('NEUTRAL',r['id'],'folds',len(ops),ops[:3],flush=True)
 for i,(a2,b2,opts)in enumerate(ops):
  Z=fold(V,a2,b2,[x[0]for x in opts]);local(V,Z,a2,b2);out=H/'local195';out.mkdir(exist_ok=True);(out/f'{r["id"]}_{i}.tm').write_text(encode(Z));allresults.append({'kind':r['id'],'drop':a2,'keep':b2,'opts':opts})
(H/'local_fold_search.json').write_text(json.dumps({'template':'Existing one-helper folds with globally forced predecessor tags; exact two-cell endpoints','base_fold_count':base_count,'neutral_recipes':neutral_results,'survivors':allresults,'scope':'Bounded negative search only, no lower bound'},indent=2)+'\n')

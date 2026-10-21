#!/usr/bin/env python3
"""Global constructor tag permutations. Exact modified CFG only, no runtime."""
from pathlib import Path
import os
import sys,json,itertools,collections
HERE=Path(__file__).resolve().parent;Z=Path(os.environ.get('PROVEIT_ZFC_ROOT', str(HERE.parent/'ProveIt/Computability/BusyBeaver/Research/ZFC'))).resolve()
sys.path.insert(0,str(Z/'k218-quantifier-stability/pricing'))
import source_language as s,build221 as b,measure_pinned as m
r=s.tree(json.loads((Z/'candidate-k218/sites218.json').read_text()));tab=b.read_table((Z/'candidate-k218/k218.native.tm').read_bytes());g,_=b.decoder_map(tab,r)
q=lambda k:b.sole(g,k);inc=('CI',1);imp=q(90);names={q(98):'a',q(12):'b',q(166):'c',imp:'I',q(19):'PUSH',q(184)[0]:'F',inc:'+1'}
tokens=[]
def walk(t,k=0):
 if t in names:tokens.append((k,names[t]));return k+len(s.sites(t))
 if s.leaf(t):tokens.append((k,str(t)));return k+1
 return walk(t[1],walk(t[0],k))
walk(r);runs=[]
for i,(at,n)in enumerate(tokens):
 if n!='I':continue
 j=i+1
 while j<len(tokens)and tokens[j][1]=='+1':j+=1
 if j>i+1:runs.append((tokens[i+1][0],j-i-1))
falsity=[at+len(s.sites(q(184)[0]))-1 for at,n in tokens if n=='F']
print('RUNS',len(runs),collections.Counter(n for _,n in runs),'F',len(falsity),flush=True)
old=s.sites(r);og=s.graph_intervals(old);assert old[4598][1:]==['CI',6]
root=HERE/'all-tag-permutations';root.mkdir(exist_ok=True);best=999
# Each option is a per-original-leaf multiplicity, and association choice for triples.
def options(n,k):
 if n==k:return[((1,)*n,0)]
 if n<k:
  return[(tuple(1+(k-n if i==j else 0)for i in range(n)),side)for j in range(n)for side in(range(2)if k-n==2 else[0])]
 return[(tuple(int(i in keep)for i in range(n)),0)for keep in itertools.combinations(range(n),k)]
records=[];trial=0
for perm in itertools.permutations((1,2,3)):
 tagmap=dict(zip((1,2,3),perm));bestp=999
 for opts in itertools.product(*(options(n,tagmap[n])for n in(1,2,3))):
  for fside,hside in itertools.product(range(2)if perm[0]==3 else[0],repeat=2):
   trial+=1;edits={}
   for at,n in runs:
    mult,side=opts[n-1]
    for j,c in enumerate(mult):edits[at+j]=(c,side)
   for at in falsity:edits[at]=(perm[0],fside)
   edits[4598]=(perm[0],hside)
   origmap={};newmap={};newindex=[0]
   def mutate(t,oi):
    if s.leaf(t):
     oldi=oi[0];oi[0]+=1;count,side=edits.get(oldi,(1,0));origmap[oldi]=newindex[0] if count else None
     if not count:return None
     for k in range(count):newmap[newindex[0]]=(oldi,k,count);newindex[0]+=1
     return t if count==1 else((t,t)if count==2 else((t,(t,t))if side==0 else((t,t),t)))
    a=mutate(t[0],oi);bb=mutate(t[1],oi)
    return bb if a is None else a if bb is None else(a,bb)
   t=mutate(r,[0]);rows=s.sites(t);ng=s.graph_intervals(rows);assert ng==s.graph_arithmetic(rows)[0]
   def target(j):
    while origmap[j]is None:j=og[j][1][0]
    return origmap[j]
   good=True
   for ni,(oi,k,count)in newmap.items():
    effect,ts=ng[ni];exp=[ni+1]if k<count-1 else[target(j)for j in og[oi][1]]
    if effect!=og[oi][0]or ts!=exp:good=False;break
   met=s.metrics(t);info=dict(trial=trial,permutation=perm,options=opts,fside=fside,hside=hside,metrics=met,cfg_pass=good)
   if good and met['dag_nodes']<=bestp:
    bestp=met['dag_nodes'];out=root/f'p{perm[0]}{perm[1]}{perm[2]}-{trial:04d}';out.mkdir(exist_ok=True);(out/'sites.json').write_bytes(s.compact(rows));(out/'result.json').write_text(json.dumps(info,indent=2));info['path']=str(out)
    print('BESTP',perm,trial,met,flush=True)
   records.append(info)
(root/'result.json').write_text(json.dumps(dict(trials=trial,records=records),indent=2));print('DONE',trial,flush=True)

#!/usr/bin/env python3
"""All 18 constructor tag assignments with nonzero membership falsity.
Source pricing only. Assignments with tag0!=I need a separate logical audit.
"""
from pathlib import Path
import os
import sys,json,itertools,collections
HERE=Path(__file__).resolve().parent;Z=Path(os.environ.get('PROVEIT_ZFC_ROOT', str(HERE.parent/'ProveIt/Computability/BusyBeaver/Research/ZFC'))).resolve()
sys.path.insert(0,str(Z/'k218-quantifier-stability/pricing'))
import source_language as s,build221 as b
r=s.tree(json.loads((Z/'candidate-k218/sites218.json').read_text()));tab=b.read_table((Z/'candidate-k218/k218.native.tm').read_bytes());g,_=b.decoder_map(tab,r)
q=lambda k:b.sole(g,k);inc=('CI',1);imp=q(90);names={q(98):'a',q(12):'b',q(166):'c',imp:'I',q(19):'PUSH',q(184)[0]:'F',inc:'+1'}
tokens=[]
def walk(t,k=0,p=''):
 if t in names:tokens.append((k,names[t],p));return k+len(s.sites(t))
 if s.leaf(t):tokens.append((k,str(t),p));return k+1
 return walk(t[1],walk(t[0],k,p+'0'),p+'1')
walk(r);runs=[]
for i,(at,n,p)in enumerate(tokens):
 if n!='I':continue
 j=i+1
 while j<len(tokens)and tokens[j][1]=='+1':j+=1
 runs.append((p,[(tokens[k][0],tokens[k][2])for k in range(i+1,j)],j-i-1))
falsity=[at+len(s.sites(q(184)[0]))-1 for at,n,p in tokens if n=='F'];old=s.sites(r);og=s.graph_intervals(old);assert old[4598][1:]==['CI',6]
print('COUNTS',collections.Counter(n for p,x,n in runs),len(falsity),flush=True)
def cat(t,k,side):
 if k==0:return None
 return t if k==1 else((t,t)if k==2 else((t,(t,t))if side==0 else((t,t),t)))
def options(n,k):
 if n==0:return[((),side)for side in(range(2)if k==3 else[0])]
 if n==k:return[((1,)*n,0)]
 if n<k:return[(tuple(1+(k-n if i==j else 0)for i in range(n)),side)for j in range(n)for side in(range(2)if k-n==2 else[0])]
 return[(tuple(int(i in keep)for i in range(n)),0)for keep in itertools.combinations(range(n),k)]
out=HERE/'all-four-tag-permutations';out.mkdir(exist_ok=True);records=[];trial=0
for perm in itertools.permutations((0,1,2,3)):
 if perm[1]==0:continue
 best=999
 for opts in itertools.product(*(options(n,perm[n])for n in range(4))):
  for fside,hside in itertools.product(range(2)if perm[1]==3 else[0],repeat=2):
   trial+=1;edits={};inode={}
   for p,ps,n in runs:
    mult,side=opts[n]
    if n==0 and perm[0]:inode[p]=(imp,cat(inc,perm[0],side))
    else:
     for (at,_),cnt in zip(ps,mult):edits[at]=(cnt,side)
   for at in falsity:edits[at]=(perm[1],fside)
   edits[4598]=(perm[1],hside)
   def mutate(t,oi,p=''):
    if p in inode:oi[0]+=len(s.sites(t));return inode[p]
    if s.leaf(t):
     oldi=oi[0];oi[0]+=1;cnt,side=edits.get(oldi,(1,0));return cat(t,cnt,side)
    a=mutate(t[0],oi,p+'0');bb=mutate(t[1],oi,p+'1')
    return bb if a is None else a if bb is None else(a,bb)
   t=mutate(r,[0]);met=s.metrics(t)
   if met['dag_nodes']<best:
    best=met['dag_nodes'];rr=s.sites(t);assert s.graph_intervals(rr)==s.graph_arithmetic(rr)[0];d=out/f'p{perm[0]}{perm[1]}{perm[2]}{perm[3]}-{trial:05d}';d.mkdir(exist_ok=True);(d/'sites.json').write_bytes(s.compact(rr));info=dict(trial=trial,permutation=perm,options=opts,metrics=met,path=str(d));(d/'result.json').write_text(json.dumps(info,indent=2));print('BEST',info,flush=True)
   records.append(dict(trial=trial,permutation=perm,metrics=met))
(out/'result.json').write_text(json.dumps(dict(trials=trial,records=records),indent=2));print('DONE',trial,flush=True)

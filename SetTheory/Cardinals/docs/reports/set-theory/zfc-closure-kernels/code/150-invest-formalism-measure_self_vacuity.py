#!/usr/bin/env python3
"""Measure K/S plus native self-vacuity by exact closed-forest replacement.

The vendored source_language.py and build221.py are unchanged ProveIt helpers;
flat/splice below are adapted unchanged in substance from the pinned
k219-pivot-fusion/code/measure.py. This checks source sizes and CFG agreement,
not binary compilation, runtime correctness, or startup.
"""
from pathlib import Path
from functools import cache
import sys,json,itertools,time,hashlib,argparse
HERE=Path(__file__).resolve().parent
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--repo',type=Path,help='Optional ProveIt checkout; exact pinned inputs are required.')
ap.add_argument('--output',type=Path,default=HERE/'reproduced_measurement')
args=ap.parse_args()
if args.repo:
 Z=args.repo/'Computability/BusyBeaver/Research/ZFC'
 helper=Z/'k219-continuation-search/compiler-inputs'
 source=Z/'candidate-k218/sites218.json';table=Z/'candidate-k218/k218.native.tm'
else:
 helper=HERE/'inputs';source=helper/'sites218.json';table=helper/'k218.native.tm'
pins={'source_language.py':'4b355b81373a06ce2d8d99f56ac88afee8bbbd934d21f4f2729d864d9807683f',
      'build221.py':'3359e8b40fefb162ca4aa1d5c5a99a368a937ec61f761c3ac6f26d573766acba',
      'sites218.json':'b0169f2d477d0584ac70f9bdb79c3a78ef2bc700d080b3cd80976210235b80d9',
      'k218.native.tm':'2dfaba6da09b78291e534777cd30c5f0d68bd84faa670e868e779c396aeb308f'}
for p in (helper/'source_language.py',helper/'build221.py',source,table):
 if hashlib.sha256(p.read_bytes()).hexdigest()!=pins[p.name]:raise ValueError(f'Pinned input differs: {p}')
args.output.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(helper))
import source_language as s
import build221 as b
@cache
def flat(n):return (n,)if isinstance(n[0],str)else flat(n[0])+flat(n[1])
def splice(s,tree,lo,hi,new):
 used=[]
 def walk(t,i=0):
  j=i+len(flat(t))
  if j<=lo or i>=hi:return t
  if lo<=i and j<=hi:
   assert s.boundary(t)==(0,0,False),('Open splice',i,j)
   if i==lo:used.append(i);return new
   return None
  assert not s.leaf(t),('Partial leaf',i,j)
  a,bb=walk(t[0],i),walk(t[1],i+len(flat(t[0])))
  return bb if a is None else a if bb is None else(a,bb)
 out=walk(tree);assert used==[lo],('Missing exact splice start',lo,hi,used)
 return out
if not __debug__:raise RuntimeError('Assertions must be enabled; do not use python -O.')
rows=json.loads(source.read_text());tree=s.tree(rows)
tab=b.read_table(table.read_bytes());groups,_=b.decoder_map(tab,tree)
q=lambda x:b.sole(groups,x)
I=lambda a,b:('I',a,b)
Q=lambda a,b:('Q',a,b)
N=lambda a:('N',a)
a,bb,c='a','b','c';imp=q(90);inc=('CI',1);neg=q(184)
mac={'a':q(98),'b':q(12),'c':q(166),'I':imp,'Q':(imp,(inc,inc)),'N':neg}
bases={'KSSV':[I(a,I(bb,a)),I(I(a,I(bb,c)),I(I(a,bb),I(a,c))),I(a,Q(a,a))],
 'KSNNSV':[I(a,I(bb,a)),I(I(a,I(bb,c)),I(I(a,bb),I(a,c))),N(N(I(a,Q(a,a))))]}

def ren(f,p):
 if not isinstance(f,tuple):return dict(zip('abc',p)).get(f,f)
 return (f[0],*(ren(x,p)for x in f[1:]))
def word(f):
 if not isinstance(f,tuple):return [f]
 return sum((word(x)for x in f[1:]),[])+[f[0]]
def join(ns,shape):
 if len(ns)==1:return ns[0]
 if shape==0:return ns[0],join(ns[1:],shape)
 if shape==1:return join(ns[:-1],shape),ns[-1]
 k=len(ns)//2;return join(ns[:k],shape),join(ns[k:],shape)
summary={};start=time.time()
for name,forms in bases.items():
 best=None;bestdata=None;besttree=None;seen=set();cnt=0
 for ps in itertools.product(list(itertools.permutations('abc')),repeat=3):
  fs=[ren(f,p)for f,p in zip(forms,ps)];ws=[word(f)for f in fs]
  for order in itertools.permutations(range(3)):
   for shape in range(3):
    local=join([join([mac[z]for z in ws[i]],shape)for i in order],shape)
    if local in seen:continue
    seen.add(local);cnt+=1
    tr=splice(s,tree,135,486,local);met=s.metrics(tr)
    key=(met['dag_nodes'],met['maximum_zero_run'],met['maximum_depth'],met['leaf_occurrences'])
    if best is None or key<best:
     best=key;besttree=tr;bestdata=dict(name=name,source_metrics=met,parameters=ps,order=order,shape=shape,words=[ws[i]for i in order])
     print('BEST',json.dumps(bestdata),flush=True)
 rr=s.sites(besttree);assert s.graph_arithmetic(rr)[0]==s.graph_intervals(rr)
 (args.output/('sites_'+name+'.json')).write_bytes(s.compact(rr))
 bestdata['unique_layouts']=cnt;summary[name]=bestdata
out={'baseline':s.metrics(tree),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'results':summary,'seconds':time.time()-start,'scope':'Literal source sizes for calibrated replacements; no binary compilation/runtime/startup claim.'}
(args.output/'self_vacuity_measurements.json').write_text(json.dumps(out,indent=2)+'\n')
print('SUMMARY',json.dumps(out),flush=True)

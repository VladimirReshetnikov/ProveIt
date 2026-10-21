#!/usr/bin/env python3
"""Independent forward replay and projection-support review. Standard library only.
Does not import the discovery checker or projection audit.
"""
from pathlib import Path
from functools import lru_cache
from collections import Counter
import json,hashlib,itertools,sys
import argparse
if not __debug__:raise RuntimeError('Run without Python optimization')
cli=argparse.ArgumentParser(description=__doc__);cli.add_argument('--certificate',type=Path,required=True);cli.add_argument('--output',type=Path,required=True);args=cli.parse_args()
P=args.certificate;D=json.loads(P.read_text())
items=[('z',)];index={items[0]:0};variables=[frozenset()]
def intern(key):
 if key not in index:
  index[key]=len(items);items.append(key)
  variables.append(frozenset([key[1]])if key[0]=='v'else variables[key[1]]|variables[key[2]])
 return index[key]
def imp(a,b):return 0 if a==b==0 else intern(('i',a,b))
def var(i):return intern(('v',i))
def parts(a):
 if a==0:return 0,0
 if items[a][0]!='i':raise ValueError('Nonimplication destructured')
 return items[a][1:]
refs=[]
for k,t in enumerate(D['term_table']):
 if t=='T':refs.append(0)
 elif isinstance(t,dict):
  assert set(t)=={'var'}and type(t['var'])is int and t['var']>=0;refs.append(var(t['var']))
 else:
  assert isinstance(t,list)and len(t)==2 and all(type(x)is int and 0<=x<k for x in t)
  refs.append(imp(refs[t[0]],refs[t[1]]))
def tref(i):assert type(i)is int and 0<=i<len(refs);return refs[i]
def substitute(term,envdata):
 env={}
 for k,v in envdata.items():assert k.isdigit()and str(int(k))==k;env[int(k)]=tref(v)
 assert variables[term]<=env.keys()
 @lru_cache(None)
 def rec(t):
  if t==0:return 0
  x=items[t]
  return env[x[1]]if x[0]=='v'else imp(rec(x[1]),rec(x[2]))
 return rec(term)
def alpha(term):
 names={}
 @lru_cache(None)
 def rec(t):
  if t==0:return 0
  x=items[t]
  if x[0]=='v':
   if x[1]not in names:names[x[1]]=len(names)
   return var(names[x[1]])
  return imp(rec(x[1]),rec(x[2]))
 return rec(term)
@lru_cache(None)
def paths(a,u):
 # Include every literal occurrence, but never project below a schema variable
 # or below the absorbing zero: zero descendants are dealt with separately.
 ans=['']if a==u else []
 if a!=0 and items[a][0]=='i':
  aa,bb=parts(a)
  ans += ['L'+p for p in paths(aa,u)]
  ans += ['R'+p for p in paths(bb,u)]
 return tuple(ans)
def project(a,p):
 for c in p:
  if a==0:continue
  if items[a][0]!='i':return None
  a=parts(a)[c=='R']
 return a
proof=[];leaves=[];counts=Counter()
for k,n in enumerate(D['nodes']):
 assert n['id']==k;t=tref(n['term']);r=n['rule'];kind=r['kind'];counts[kind]+=1
 if kind=='truth':assert t==0
 elif kind=='dominated_rho8':
  pre,post=parts(t);cu,a=parts(pre);c,u=parts(cu);ac,bc=parts(post);a2,c2=parts(ac);b,c3=parts(bc)
  assert a==a2 and c==c2==c3
  ps=paths(a,u)
  assert u==0 or ps
  leaves.append({'node':k,'a':a,'u':u,'paths':list(ps)})
 elif kind=='substitution':
  p=r['parent'];assert type(p)is int and 0<=p<k
  assert substitute(proof[p],r['substitution'])==t
 elif kind in('mp','mp_substitution'):
  ma,mi=r['major'],r['minor'];assert all(type(j)is int and 0<=j<k for j in(ma,mi));major,minor=proof[ma],proof[mi]
  if kind=='mp_substitution':
   major=substitute(major,r['major_substitution']);minor=substitute(minor,r['minor_substitution'])
  ant,con=parts(major);assert ant==minor
  assert alpha(con)==alpha(t)if kind=='mp_substitution'else con==t
 else:raise ValueError(kind)
 proof.append(t)
p,q,r=[var(j)for j in range(3)];a,b,c,u=[var(j)for j in range(4)]
expected={'I':imp(p,p),'K':imp(p,imp(q,p)),'P':imp(imp(imp(p,q),p),p),'cd59':imp(imp(p,q),imp(imp(imp(p,r),p),q)),'B':imp(imp(p,q),imp(imp(q,r),imp(p,r))),'S':imp(imp(p,imp(q,r)),imp(imp(p,q),imp(p,r))),'rho8':imp(imp(imp(c,u),a),imp(imp(a,c),imp(b,c)))}
assert set(D['roots'])==set(expected)
for name,t in expected.items():assert alpha(proof[D['roots'][name]])==alpha(t)
words=sorted(set(p for x in leaves if x['u']!=0 for p in x['paths']),key=lambda p:(len(p),p))
# Any projection that covers a nonzero leaf belongs to this finite universe.
# Words outside it cover only zero leaves, where the constant-zero family dominates.
universe=['ZERO']+words
coverage=[]
for x in leaves:
 choices=[p for p in universe if (x['u']==0 if p=='ZERO'else project(x['a'],p)==x['u'])]
 assert choices;coverage.append(set(choices))
forced={next(iter(s)) for s in coverage if len(s)==1}
forced_witnesses={p:next(x['node']for x,s in zip(leaves,coverage)if s=={p})for p in sorted(forced)}
minimum=None;optima=[]
if True:
 for k in range(len(forced),10):
  for rest in itertools.combinations([p for p in universe if p not in forced],k-len(forced)):
   selected=forced|set(rest)
   if all(s&selected for s in coverage):optima.append(sorted(selected,key=lambda p:(p!='ZERO',len(p),p)))
  if optima:minimum=k;break
selected=['ZERO','','L','R','LL','RR','LLR','RRR','LLRR']
assert all(s&set(selected)for s in coverage)
report={'status':'INDEPENDENT_FORWARD_AND_PROJECTOR_REVIEW_PASS','input':str(P),'sha256':hashlib.sha256(P.read_bytes()).hexdigest(),'proof_nodes':len(proof),'source_terms':len(refs),'rules':dict(counts),'all_roots_verified':list(expected),'restricted_leaf_count':len(leaves),'projection_universe':['epsilon'if p==''else p for p in universe],'forced_families':{'epsilon'if p==''else p:n for p,n in forced_witnesses.items()},'minimum_literal_certificate_cover':minimum,'optimal_covers':[['epsilon'if p==''else p for p in s]for s in optima],'support_basis_cardinality':len(selected),'disjoint_lower_bound_witnesses':{str(node):sorted(s)for x,s in zip(leaves,coverage)for node in[115,1112,2163]if x['node']==node},'scope':'Independent forward replay of the exact symbolic certificate, numerical schematic interpretation reviewed separately. Minimum applies to covering this exact certificate by constant-zero or literal projection families, not minimal equiconsistent calculi or machines.'}
args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

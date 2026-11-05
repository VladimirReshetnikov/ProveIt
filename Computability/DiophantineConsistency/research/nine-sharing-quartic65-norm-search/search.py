#!/usr/bin/env python3
"""Bounded search with five separate norm residuals, not the product."""
import collections,hashlib,json,random,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];f=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';raw=f.read_bytes();assert hashlib.sha256(raw).hexdigest()=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e';g=json.loads(raw);rows=g['source'][:60];terminal={'N0','N1','Nt','Na','scaled_Ns'};names=[x[0] for x in rows if x[0] not in terminal];rng=random.Random(20261105);mx=lambda a,b:b if a is None else a if b is None else max(a,b);mul=lambda a,b:None if a is None or b is None else a+b;cache={}
def run(cuts):
 key=frozenset(cuts)
 if key in cache:return cache[key]
 env={n:(1,None) for n in g['witnesses']};env.update({n:(0,None) for n in g['fixed_numerals']});cost=0
 for n,op,a,b in rows:
  get=lambda x:(0,None) if type(x)==int else env[x];ap,an=get(a);bp,bn=get(b)
  if op=='+':x,y=mx(ap,bp),mx(an,bn)
  elif op=='-':x,y=mx(ap,bn),mx(an,bp)
  else:x,y=mx(mul(ap,bp),mul(an,bn)),mx(mul(ap,bn),mul(an,bp))
  if mx(x,y)>2:
   opts=sorted(set(j for j in (a,b) if isinstance(j,str) and j not in cuts and j in names and mx(*env[j])>1));assert opts,(n,a,b,cuts);cache[key]=(False,cost,opts);return cache[key]
  if n in cuts:
   assert n not in terminal;cost+=1 if y is None else 2;env[n]=(1,None if y is None else 1)
  else:env[n]=(x,y)
 cache[key]=(True,cost,[]);return cache[key]
def repair(cuts):
 c=set(cuts)
 while True:
  valid,cost,opts=run(c)
  if valid:return c
  c.add(rng.choice(opts))
def prune(cuts):
 c=set(cuts);order=list(c);rng.shuffle(order)
 for n in order:
  q=c-{n};valid,cost,_=run(q)
  if valid and cost<=run(c)[1]:c=q
 return c
baseline={'Dc2','Delta','E','V','V2minusY2','X','Y','c2','cTminusR','ell','f2','gap','kY','main_root','main_square','normalized_S','normalized_S2','q2','q3','scaled_f2','tau'}
baseline=repair(baseline);best=prune(baseline);pool=[best];distribution=collections.Counter();iterations=5000
for i in range(iterations):
 c=set(rng.choice(pool));nflip=1+rng.randrange(5)
 for n in rng.sample(names,nflip):
  if n in c:c.remove(n)
  else:c.add(n)
 c=prune(repair(c));ok,cost,_=run(c);assert ok;distribution[14+cost]+=1
 if (cost,len(c),sorted(c))<(run(best)[1],len(best),sorted(best)):best=c
 if c not in pool:pool.append(c);pool.sort(key=lambda x:(run(x)[1],len(x),sorted(x)));pool=pool[:80]
print(json.dumps({'status':'PASS_BOUNDED_DEGREE_SEARCH','iterations':iterations,'random_seed':20261105,'visited_cut_sets':len(cache),'baseline_witnesses':14+run(baseline)[1],'best_witnesses':14+run(best)[1],'best_cut_count':len(best),'best_cuts':sorted(best),'distribution':dict(sorted(distribution.items())),'scope':'Heuristic degree-feasible cuts after replacing product by five separate norm conditions; not yet a candidate, model bridge or global optimality.'},indent=2,sort_keys=True))

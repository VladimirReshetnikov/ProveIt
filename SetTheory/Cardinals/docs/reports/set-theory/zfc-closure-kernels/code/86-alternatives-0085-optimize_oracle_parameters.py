#!/usr/bin/env python3
"""Exact finite parameter-renaming search for the fixed-template Mealy oracle.

The bundle's parameter order is fixed so its two freshness tests keep exactly
positions (2,0),(2,1). Logical schema parameter fields may be permuted because
all assignments are quantified; the chosen format specifies those orders.
"""
if not __debug__:
    raise RuntimeError('Assertions must be enabled; do not use python -O.')


import itertools,json,time
import pattern_oracle as O

C,P,T=O.load_source()
roots={k:O.unroll(t,t.root) for k,t in T.items()}
def rename(t,p):
 if t[0]=='z':return t
 if t[0]=='p':return ('p',p[t[1]])
 return (t[0],rename(t[1],p),rename(t[2],p))
variants={}
universe=set()
for k,t in T.items():
 vv=[]
 perms=[tuple(range(t.arity))] if k==11 else itertools.permutations(range(t.arity))
 for perm in perms:
  rt=rename(roots[k],perm);nodes=O.constructor_set({k:rt});universe.update(nodes)
  vv.append((perm,nodes,rt))
 variants[k]=vv
ids={n:i for i,n in enumerate(sorted(universe,key=repr))}
for k,vv in variants.items():
 variants[k]=[(p,sum(1<<ids[n] for n in nn),rt) for p,nn,rt in vv]
base=variants[11][0][1]
order=sorted([k for k in T if k!=11],key=lambda k:(-min((mask&~base).bit_count() for p,mask,t in variants[k]),len(variants[k])))
bestmask=base
best={11:variants[11][0][0]}
for k in order:
 p,mask,rt=min(variants[k],key=lambda item:(item[1]&~bestmask).bit_count());bestmask|=mask;best[k]=p
bestcount=bestmask.bit_count();stats={'entered':0,'pruned':0,'leaves':0}
t0=time.monotonic()
def search(i,mask,choices):
 global bestcount,best,bestmask
 stats['entered']+=1
 if mask.bit_count()>=bestcount:
  stats['pruned']+=1;return
 if i==len(order):
  stats['leaves']+=1;bestcount=mask.bit_count();best=dict(choices);bestmask=mask;return
 # Every remaining template has to fit; maximal individually unavoidable addition
 # is a safe lower bound (summing additions would be unsafe due to sharing).
 minextra=max(min((vm&~mask).bit_count() for p,vm,t in variants[k]) for k in order[i:])
 if mask.bit_count()+minextra>=bestcount:
  stats['pruned']+=1;return
 k=order[i]
 for p,vm,rt in sorted(variants[k],key=lambda item:(item[1]&~mask).bit_count()):
  search(i+1,mask|vm,{**choices,k:p})
search(0,base,{11:variants[11][0][0]})
result={'scope':'Exact finite optimum for independent parameter permutations of eight unchanged logical templates; bundle fixed.',
'original_constructor_states':91,'minimum_constructor_states':bestcount,'permutations':best,
'naive_assignment_product':__import__('math').prod(len(v) for v in variants.values()),
'universe_nodes':len(universe),'order':order,'search':stats,'elapsed_seconds':time.monotonic()-t0}
print(json.dumps(result,indent=2))
(__import__('pathlib').Path(__file__).parent/'oracle_parameter_search.json').write_text(json.dumps(result,indent=2)+'\n')

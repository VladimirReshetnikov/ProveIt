#!/usr/bin/env python3
"""Independent boundary, collision permutation, and inverse checks."""
import importlib.util, json, random, sys, hashlib
from collections import defaultdict
from pathlib import Path
src=Path(__file__).with_name('three_mass_collision_generator.py')
spec=importlib.util.spec_from_file_location('candidate',src)
m=importlib.util.module_from_spec(spec);sys.modules[spec.name]=m;spec.loader.exec_module(m)
I=m.Instruction
ca=m.ThreeMassCA(['a','b','c','d','halt'],'halt',[
 I('a','b','inc',0),I('b','c','inc',1),I('c','d','dec',0),I('d','a','dec',1)])
# Check the completed pair map as a relation, independently of row() assertions.
assert set(ca.pairs)==set(ca.pairs.values())
assert len(ca.pairs)==len(set(ca.pairs.values()))
for inp,out in ca.pairs.items():
 assert len(set(inp))==len(set(out))==2
 assert ca.pair_preimage[out]==inp
sinv={v:k for k,v in ca.single.items()}
assert len(sinv)==len(ca.single)==len(ca.names)
def inverse(conf):
 cells=defaultdict(list)
 for x,t in conf:cells[x-ca.velocity[t]].append(t)
 result=[]
 for x,tt in cells.items():
  tt=tuple(sorted(tt));assert len(set(tt))==len(tt)
  oo=(sinv[tt[0]],) if len(tt)==1 else ca.pair_preimage.get(tt,tt) if len(tt)==2 else tt
  result.extend((x,t) for t in oo)
 return tuple(sorted(result))
rng=random.Random(20261002)
random_cases=3000
for _ in range(random_cases):
 mass=rng.randrange(1,8)
 conf=tuple(sorted(set((rng.randrange(-4,5),rng.randrange(len(ca.names))) for _ in range(mass))))
 assert inverse(ca.step(conf))==conf
 assert ca.step(inverse(conf))==conf
# Boundary checks at all six scratch values and across multiple clock wraps.
queries=0
for N in [1,2,3,4,5,6,7,11,12,13,18,25]:
 for z in range(6):
  for eps,stage,stop in [(1,0,1),(-1,2,3)]:
   conf=ca.initial('a',N,i=3,z=z,stage=stage)
   init=conf
   for tick in range(1,48*N+2):
    prev=conf;conf=ca.step(conf,require_specified=True)
    assert inverse(conf)==prev
    if tick<48*N+1:
     assert conf!=ca.initial('a',N,i=3,z=(z+eps*N)%6,stage=stop)
   assert conf==ca.initial('a',N,i=3,z=(z+eps*N)%6,stage=stop)
   queries+=1
# Arithmetic uses exactly L/q+1 ticks and reaches no completion rows.
arithmetic=0
for j,ins in enumerate(ca.instructions,1):
 p,q=((2,3)[ins.counter],1) if ins.operation=='inc' else (1,(2,3)[ins.counter])
 for N in range(1,49):
  if N%q:continue
  conf=ca.initial('a',N,i=j,z=5,stage=4)
  stop=ca.initial('a',p*N//q,i=j,z=5,stage=5)
  for tick in range(1,12*N//q+2):
   prev=conf;conf=ca.step(conf,require_specified=True)
   assert inverse(conf)==prev
   if tick<12*N//q+1:assert conf!=stop
  assert conf==stop
  arithmetic+=1
report={'status':'PASS','source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),
 'pair_support':len(ca.pairs),'random_global_inverse_cases':random_cases,
 'query_cases':queries,'arithmetic_cases':arithmetic,
 'query_ticks':'4L+1','arithmetic_ticks':'L/q+1',
 'instruction_ticks':'8L+8Lprime+L/q+8 (motion); 16L+8 (test/no-op)'}
print(json.dumps(report,indent=2))


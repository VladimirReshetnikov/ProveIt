#!/usr/bin/env python3
"""Export proved source-local constant and interval facts for richer Box runs."""
from pathlib import Path
from fractions import Fraction as F
import gzip,json,sys
import mp_affine_nonnegative as a
ROOT=Path(__file__).resolve().parents[1]
src=ROOT/'compression/mp_newperm_gap43_phase_native'
out=ROOT/'compression/mp_invariant_box_native';out.mkdir(exist_ok=True)
for name in ('native_table.txt','native_cases.txt','native_usage.txt'):(out/name).write_bytes((src/name).read_bytes())
with gzip.open(ROOT/'compression/mp_affine_nonnegative_spaces.json.gz','rt') as f:raw=json.load(f)
spaces=[None if rows is None else tuple(tuple(F(n,d) for n,d in row) for row in rows) for rows in raw]
logical_to_physical=[3,1,0,6,2,4,7,8,5]
count=0;constants={};largest=0
with (out/'native_bounds.txt').open('w') as f:
 for line in (src/'native_cases.txt').read_text().splitlines():
  i=int(line.split()[0]);site,pc,op,r,zero=a.ctx.cases[i]
  masks=list(a.ctx.values[site]);space=spaces[site]
  if op=='CD':
   masks[r]&=1 if zero else 6
   if zero:space=a.meet_coordinate(space,r,0)
  space=a.refine(space,masks)
  assert space is not None,(i,pc)
  lower=[0]*9;upper=[-1]*9
  for logical,mask in enumerate(masks):
   physical=logical_to_physical[logical]
   lo=0 if mask&1 else 1 if mask&2 else 2
   hi=1 if mask&2 and not mask&4 else 0 if mask==1 else -1
   const=a.is_constant(space,logical)
   if const is not None:
    assert const.denominator==1 and const>=0
    n=int(const);largest=max(largest,n);constants[str(n)]=constants.get(str(n),0)+1
    if n<=100000000:lo=hi=n
    else:lo,hi=100000000,-1
   lower[physical]=lo;upper[physical]=hi
  fields=[i]
  for lo,hi in zip(lower,upper):
   assert hi<0 or lo<=hi
   fields.extend([lo,hi])
  f.write(' '.join(map(str,fields))+'\n');count+=1
meta=json.loads((src/'metadata.json').read_text());meta.update({'invariant_box_cases':count,'constant_occurrences':constants,'largest_constant':largest,'logical_to_physical':logical_to_physical})
(out/'metadata.json').write_text(json.dumps(meta,indent=2)+'\n')
print('Rich Box intervals exported:',count,'cases; largest exactconstant',largest)

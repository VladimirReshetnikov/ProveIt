"""Exact bounded-space intersection of the extended depth-five relation family."""
from pathlib import Path
from fractions import Fraction as Q
from collections import defaultdict
import hashlib,json,math,time
V=Path(__file__).resolve().parent
source=V/'S6-depth-five-extended-probe.json';probe=json.loads(source.read_text());basis={};bounded=[];seen=set();zero=0;started=time.monotonic()
def add(x,y,a):
 for k,c in y.items():
  z=x.get(k,Q(0))+a*c
  if z:x[k]=z
  elif k in x:del x[k]
for row_id,item in enumerate(probe['rows']):
 poly={tuple(z['word']):Q(z['coefficient']) for z in item['projected_relation']};top={w:c for w,c in poly.items() if sum(x!=0 for x in w)>4};low={w:c for w,c in poly.items() if sum(x!=0 for x in w)<=4};combo={row_id:Q(1)}
 assert all(sum(x!=0 for x in w)==5 for w in top)
 while top:
  pivot=min(top);a=top[pivot]
  if pivot not in basis:
   scale=1/a;basis[pivot]=({w:c*scale for w,c in top.items()},{w:c*scale for w,c in low.items()},{j:c*scale for j,c in combo.items()});break
  b,bl,bc=basis[pivot];add(top,b,-a);add(low,bl,-a);add(combo,bc,-a)
 else:
  if not low:zero+=1;continue
  den=math.lcm(*(c.denominator for c in low.values()));ints={w:c.numerator*(den//c.denominator) for w,c in low.items()};g=math.gcd(*ints.values());factor=Q(den,g)
  if ints[min(ints)]<0:factor=-factor
  low={w:c*factor for w,c in low.items()};assert all(c.denominator==1 for c in low.values());combo={j:c*factor for j,c in combo.items()};key=tuple(sorted(low.items()))
  if key not in seen:
   seen.add(key);bounded.append(dict(integer_relation=[dict(word=list(w),coefficient=int(c)) for w,c in sorted(low.items())],source_combination=[dict(row=j,coefficient=str(c)) for j,c in sorted(combo.items())]))
 if (row_id+1)%20==0:print('Exact top-sector elimination',row_id+1,'rank',len(basis),'bounded relations',len(bounded),flush=True)
# Reconstruct every retained bounded combination directly from the original
# exact projected rows, checking all outside coordinates vanish.
for b in bounded:
 q=defaultdict(Q)
 for x in b['source_combination']:
  a=Q(x['coefficient'])
  for z in probe['rows'][x['row']]['projected_relation']:q[tuple(z['word'])]+=a*Q(z['coefficient'])
 q={w:c for w,c in q.items() if c};expected={tuple(z['word']):Q(z['coefficient']) for z in b['integer_relation']};assert q==expected and all(sum(x!=0 for x in w)<=4 for w in q)
result=dict(status='PASS',input_rows=len(probe['rows']),top_sector_exact_rank=len(basis),kernel_dimension=len(probe['rows'])-len(basis),nonzero_distinct_bounded_relations=len(bounded),zero_bounded_combinations=zero,bounded_relations=bounded,source_probe_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),elapsed_seconds=round(time.monotonic()-started,3),scope='Exact rational elimination of every depth-five component, carrying all lower components and source combinations. These rows span the bounded-space information obtainable from the selected 190 projected DS inputs. Each retained row is independently reconstructed from those inputs; no outside coordinate is silently dropped. This intersection certificate does not itself prove S6.')
(V/'S6-depth-five-bounded-intersection.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8');print('Exact bounded intersection complete:',len(basis),'top pivots;',len(bounded),'new bounded relations')

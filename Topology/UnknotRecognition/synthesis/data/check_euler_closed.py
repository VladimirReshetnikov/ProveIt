import random
from fastunknot import Diagram
from fastunknot.scan_fast import FastScan
from fastunknot.euler_scan import SuffixEuler

def closed_euler(pd,order,stage,pairs):
 rows=[pd[i] for i in order[stage:]]
 if not rows:
  assert not pairs
  return 1
 occurrences={}
 for i,row in enumerate(rows):
  for j,label in enumerate(row):
   occurrences.setdefault(label,[]).append(4*i+j)
 alpha=[-1]*(4*len(rows))
 for ends in occurrences.values():
  if len(ends)==2:
   a,b=ends
   alpha[a]=b;alpha[b]=a
 for l,r in pairs:
  a,=occurrences[l]; b,=occurrences[r]
  alpha[a]=b; alpha[b]=a
 assert min(alpha)>=0
 seen=set();enters=set();components=0
 for start in range(len(alpha)):
  if start in seen: continue
  components+=1
  d=start
  while d not in seen:
   enters.add(d)
   opposite=d^2
   seen.add(d);seen.add(opposite)
   d=alpha[opposite]
  assert d==start
 negatives=0
 for i in range(len(rows)):
  under=0 if 4*i in enters else 2
  over=1 if 4*i+1 in enters else 3
  negatives+=(over-under)%4!=3
 return (-1 if negatives%2 else 1)*(1<<components)

rng=random.Random(10261007)
checked=0;states=0
while checked<500:
 strands=rng.randrange(2,6)
 word=[rng.choice([-1,1])*rng.randrange(1,strands) for _ in range(rng.randrange(strands-1,16))]
 try:d=Diagram.from_braid(strands,word)
 except ValueError:continue
 order=list(range(len(word)));rng.shuffle(order)
 engine=SuffixEuler(d.pd,order,max_states=100000)
 scan=FastScan(shape_cache=False)
 for stage in range(len(order)+1):
  for matching in {m for m in scan.mid if m is not None}:
   pairs=scan.algebra.pairs[matching]
   actual=closed_euler(d.pd,order,stage,pairs)
   expected=engine.evaluate(stage,pairs)
   states+=1
   if actual!=expected:
    print('MISMATCH',word,order,stage,pairs,actual,expected);raise SystemExit(1)
  if stage<len(order):scan.add_crossing(d.pd[order[stage]])
 checked+=1
print('OK',checked,'diagrams',states,'states')

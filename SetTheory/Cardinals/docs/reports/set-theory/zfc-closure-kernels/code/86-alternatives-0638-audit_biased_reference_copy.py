#!/usr/bin/env python3
"""Independent sparse whole-tape checks of the emitted 21-state biased reference copier."""
from pathlib import Path
import hashlib,importlib.util,itertools,json,random,sys
if not __debug__:raise RuntimeError('Assertions required')
OUT=Path(__file__).resolve().parent;D=OUT.parent/'native_copier'
sys.path.insert(0,str(D))
s=importlib.util.spec_from_file_location('biased_copy_review',D/'biased_reference_copy.py');M=importlib.util.module_from_spec(s);s.loader.exec_module(M)
def parse(p):
 rows={}
 for line in p.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n));assert (q,b)not in rows
  assert b in (0,1) and w in (0,1) and d in ('L','R');rows[q,b]=w,d,n
 return rows
T=parse(D/'biased_reference_copy_21.tm');compiled,start,ret,ids=M.compile_copy()
assert T==compiled and start==0 and ret==21
assert set(T)==set(itertools.product(range(21),range(2)))
assert all(0<=n<=21 for w,d,n in T.values())
seen=set();count=0;maxsteps=0;boundary={str(v):0 for v in (0,1,2)}
def check(v,previous,gap,c,mask):
 global count,maxsteps
 # Build independently. Future cells are arbitrary, not required to be fields.
 ones={c,c+gap+1};p=c+gap+3
 for a in previous:
  ones.update(range(p,p+a+1));p+=a+2
 source=p;ones.update(range(source+1,source+v+3));delimiter=source+v+3
 for k in range(8):
  if mask>>k&1:ones.add(c-1-k)
  if mask>>(7-k)&1:ones.add(delimiter+1+k)
 want=ones|{source}|set(range(c,c+v+1));tape=set(ones);q=0;h=source;steps=0;lo=hi=h
 while q!=21:
  assert steps<1000000
  lo=min(lo,h);hi=max(hi,h);b=int(h in tape);seen.add((q,b));w,d,q=T[q,b]
  if w:tape.add(h)
  else:tape.discard(h)
  h+=1 if d=='R'else-1;steps+=1
 assert tape==want and h==c+v,(v,previous,gap,c,mask,sorted(tape^want),h)
 assert lo>=c and hi<=delimiter
 count+=1;maxsteps=max(maxsteps,steps)
 if v in (0,1,2):boundary[str(v)]+=1
for length in range(4):
 for previous in itertools.product(range(3),repeat=length):
  for v in (0,1,2,3,4,9):
   for extra,c,mask in ((2,0,0),(2,-31,255),(3,7,85),(11,23,170)):
    check(v,previous,v+extra,c,mask)
rng=random.Random(301826)
for _ in range(300):
 previous=tuple(rng.randrange(20)for _ in range(rng.randrange(15)))
 v=rng.randrange(80);check(v,previous,v+rng.randrange(2,50),rng.randrange(-100,100),rng.randrange(256))
assert set(q for q,b in seen)==set(range(20))
r={'status':'PASS','working_states':21,'operational_states':20,'separate_return':21,'rows':42,
 'independent_whole_tape_cases':count,'boundary_cases':boundary,'max_steps':maxsteps,'valid_operational_states_exercised':len(set(q for q,b in seen)),
 'valid_transition_rows_exercised':len(seen),'scope':'Valid prepared-frame copier only; arbitrary exterior cells preserved. Universal proof in biased_reference_copy_review.md.',
 'hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in(D/'biased_reference_copy.py',D/'biased_reference_copy_21.tm')}}
(OUT/'biased_reference_copy_independent_audit.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))

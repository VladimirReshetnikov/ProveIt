"""Finite cylinder search for recycling a left-scanner control.

The enumerated bits are arbitrary; a successful case must exit before touching
an unenumerated cell. This searches exact local replacements, not long-run tests.
"""
import itertools,json,hashlib
from pathlib import Path
HERE=Path(__file__).resolve().parent
path=HERE/'input.native.tm'
rows={}
for line in path.read_text().splitlines():
 if not line.strip() or line.startswith('#'):continue
 q,b,w,d,n=line.split();rows[int(q),int(b)]=(int(w),d=='R',int(n))
controls=sorted({q for q,b in rows})
chain=[2,3,5,9,15,23,34]
results=[]
for depth,q in enumerate(chain[1:],1):
 cases=[]
 for bits in itertools.product((0,1),repeat=7):
  tape={i:b for i,b in zip([-3,-2,-1,0,depth+1,depth+2,depth+3],bits)}
  tape.update({i:0 for i in range(1,depth+1)})
  w,d,n=rows[q,tape[0]];target_tape=dict(tape);target_tape[0]=w
  cases.append((tape,(n,1 if d else -1,target_tape)))
 for candidate in controls:
  if candidate==q:continue
  clocks=[]
  for case_index,(tape,target) in enumerate(cases):
   st,h=candidate,0;tt=dict(tape)
   for clock in range(1,41):
    if st==q or h not in tt or (st,tt[h])not in rows:break
    w,d,st=rows[st,tt[h]];tt[h]=w;h+=1 if d else -1
    if (st,h,tt)==target:
     clocks.append(clock);break
   else:pass
   if len(clocks)!=case_index+1:break
  if len(clocks)==len(cases):results.append(dict(state=q,replacement=candidate,history_zeros=depth,cases=len(cases),max_clock=max(clocks)))
receipt=dict(input_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),controls=len(controls),deletions=6,candidates=6*(len(controls)-1),maximum_local_steps=40,arbitrary_bits_per_cylinder=7,history_depths=list(range(1,7)),results=results,scope='Exact old-one-step endpoint replacements in these bounded local cylinders. No general minimality claim.')
(HERE/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))

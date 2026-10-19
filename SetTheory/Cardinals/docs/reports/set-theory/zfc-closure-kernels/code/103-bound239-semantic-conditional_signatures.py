from pathlib import Path
import json, random, time
import scan_semantics as s
HERE=Path(__file__).resolve().parent
started=time.monotonic();zero=(0,)*9
nodes=[n for n in range(len(s.S)) if s.closed(n) and s.run(n,zero) is not None]
out=[];rng=random.Random(94611)
for a in nodes:
 for b in nodes:
  if len(s.leaves(b))>=len(s.leaves(a)):continue
  if s.run(a,zero)[0]!=s.run(b,zero)[0]:continue
  required=[]
  for j in range(9):
   for v in (1,2,4):
    inp=tuple(v if i==j else 0 for i in range(9))
    x,y=s.run(a,inp),s.run(b,inp)
    if x is None or y is None or x[0]!=y[0]:required.append(j);break
  if len(required)>3:continue
  for _ in range(20):
   inp=tuple(0 if i in required else rng.randrange(5) for i in range(9))
   x,y=s.run(a,inp),s.run(b,inp)
   if x is None or y is None or x[0]!=y[0]:break
  else:
   out.append({'from_node':a,'to_node':b,'from_leaves':len(s.leaves(a)),'to_leaves':len(s.leaves(b)),
      'zero_registers':required,'from_controls':[q for q,ns in s.D['qnodes'].items() if ns==[a]],
      'to_controls':[q for q,ns in s.D['qnodes'].items() if ns==[b]],
      'from_source':s.S[a],'to_source':s.S[b]})
res={'status':'FINITE_HEURISTIC_ONLY','matches':out,'seconds':time.monotonic()-started}
(HERE/'conditional_signatures.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps(res,indent=2))

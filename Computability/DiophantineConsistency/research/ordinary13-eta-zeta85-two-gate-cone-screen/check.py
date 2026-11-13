from pathlib import Path
from collections import defaultdict
from hashlib import sha256
import json,random,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
p=Path('research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json');raw=p.read_bytes();h=sha256(raw).hexdigest()
assert h=='ce50ab07246ad3fb77ad787fa5703fd64a8dfd94a346308b73f891225cb36f03'
g=json.loads(raw);rows=g['source'];inputs=g['witnesses']+g['fixed_numerals'];assert len(rows)==85 and len(inputs)==17
prime=1000000007;seed=421658;rng=random.Random(seed);samples=[]
for _ in range(5):
 d={x:rng.randrange(1,prime) for x in inputs}
 for n,op,x,y in rows:
  x=x if type(x)==int else d[x];y=y if type(y)==int else d[y]
  d[n]=({'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]())%prime
 samples.append(d)
uses=defaultdict(set);lookup={r[0]:r for r in rows}
for n,_,x,y in rows:
 for v in (x,y):
  if type(v)==str:uses[v].add(n)
def val(s,v):return (v if type(v)==int else s[v])%prime
cones=[];survivors=[];first_matches=0;total_candidates=0
for idx,(target,_,_,_) in enumerate(rows):
 cone={target};changed=True
 while changed:
  changed=False
  for name in tuple(cone):
   for x in lookup[name][2:]:
    if type(x)==str and x in lookup and x not in cone and uses[x]<=cone:
     cone.add(x);changed=True
 if len(cone)<3:continue
 avail=inputs+[r[0] for r in rows[:idx] if r[0] not in cone]+[0,1,2,3,4]
 assert len(avail)==len(set(avail))
 t=val(samples[0],target);assert t!=0
 need=defaultdict(list)
 for z in avail:
  a=val(samples[0],z)
  need[(t-a)%prime].append(('+',z,0))
  need[(t+a)%prime].append(('-',z,0))
  need[(a-t)%prime].append(('-',z,1))
  if a:need[(t*pow(a,prime-2,prime))%prime].append(('*',z,0))
 # First gate: 3 ordered operations on N² pairs; second gate: 4N
 # arrangements with an old wire, plus u+u, u-u and u*u.
 total_candidates+=3*len(avail)**2*(4*len(avail)+3)
 for x in avail:
  a=val(samples[0],x)
  for y in avail:
   b=val(samples[0],y)
   for op,u in (('+',(a+b)%prime),('-',(a-b)%prime),('*',(a*b)%prime)):
    matches=list(need.get(u,()))
    if (2*u)%prime==t:matches.append(('+','SELF',0))
    if (u*u)%prime==t:matches.append(('*','SELF',0))
    # u-u=0 and multiplication by the old wire 0 cannot match t≠0.
    first_matches+=len(matches)
    for op2,z,reverse in matches:
     same=True
     for sample in samples[1:]:
      vx=val(sample,x);vy=val(sample,y);vt=val(sample,target)
      v1=(vx+vy if op=='+' else vx-vy if op=='-' else vx*vy)%prime
      vz=v1 if z=='SELF' else val(sample,z)
      v2=(v1+vz if op2=='+' else (vz-v1 if reverse else v1-vz) if op2=='-' else v1*vz)%prime
      if v2!=vt:same=False;break
     if same:survivors.append([target,sorted(cone),x,op,y,op2,z,reverse])
 cones.append({'target':target,'removed_cone_size':len(cone),'available_wires':len(avail),'target_first_residue':t})
print(json.dumps({'graph_sha256':h,'modulus':prime,'rng_seed':seed,'sample_input_assignments':[{x:d[x] for x in inputs} for d in samples], 'cones':cones,'cone_count':len(cones),'two_gate_candidates':total_candidates,'matches_first_assignment':first_matches,'survivors_all_five':survivors,'lean_executed':False,'scope':'For each maximal internally used predecessor cone with at least three gates, exact-output replacement by two binary gates over earlier non-cone wires and literals 0..4 only. A nonmatch modulo the prime is a counterexample to an integer polynomial identity; no zero-set or global lower bound is asserted.'},sort_keys=True,indent=2))

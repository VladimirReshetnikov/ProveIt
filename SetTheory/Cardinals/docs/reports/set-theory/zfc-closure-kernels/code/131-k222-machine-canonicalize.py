#!/usr/bin/env python3
"""Exact deterministic renumbering and independent full blank startup of K222."""
from pathlib import Path
from collections import Counter
import hashlib,json
D=Path(__file__).resolve().parent
raw=(D/'k222.native.tm').read_bytes()
assert hashlib.sha256(raw).hexdigest()=='a85b0baf596c5559581344d02b0fb263f97dda2f9a0781f6c7e651cd236fd818'
t={};starts=[]
for line in raw.decode('ascii').splitlines():
 if line.startswith('#! start '):starts.append(int(line.split()[-1]))
 elif line and not line.startswith('#'):
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
  assert (q,b) not in t and b in(0,1) and w in(0,1) and d in('L','R')
  t[q,b]=(w,d,z)
s={q for q,b in t};assert starts==[0] and len(s)==222 and set(t)=={(q,b)for q in s for b in(0,1)}
assert {z for w,d,z in t.values()}-s=={254}
order=[0];mp={0:0}
for q in order:
 for b in(0,1):
  z=t[q,b][2]
  if z in s and z not in mp:mp[z]=len(order);order.append(z)
assert set(order)==s
mp[254]=222
ct={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in t.items()}
encoded='#! start 0\n'+''.join(f'{q} {b} {w} {d} {z}\n'for(q,b),(w,d,z)in sorted(ct.items()))
(D/'k222.tm').write_text(encoded)
# Both tables run independently, tracking the entire nonblank support.
def run(tab):
 q,h,ones,vis=0,0,set(),Counter()
 for i in range(409835):
  b=int(h in ones);vis[q,b]+=1;w,d,q=tab[q,b]
  if w:ones.add(h)
  else:ones.discard(h)
  h+=1 if d=='R' else -1
 return q,h,ones,vis
logical=[3,0,0,0,3,0,0,0,0];physical=[None]*9
for i,j in enumerate([6,2,0,4,3,7,8,5,1]):physical[j]=logical[i]
expected={-6,176};cursor=177
for n in physical+[1]*167:
 cursor+=1
 expected.update(range(cursor,cursor+n+1));cursor+=n+1
q,h,ones,vis=run(t);cq,ch,cones,cvis=run(ct)
assert (q,h,ones)==(84,-5,expected) and (cq,ch,cones)==(mp[84],-5,expected)
assert cvis==Counter({(mp[q],b):n for(q,b),n in vis.items()})
r=dict(status='EXACT_CANONICALIZATION_AND_COMPLETE_BLANK_STARTUP_PASS',working_states=222,rows=444,start=0,halt=222,dispatcher=mp[84],native_to_canonical=mp,canonical_to_native={v:k for k,v in mp.items()},rule='Breadth first, read0 before read1; terminal254 maps to222',native_sha256=hashlib.sha256(raw).hexdigest(),canonical_sha256=hashlib.sha256(encoded.encode()).hexdigest(),source_sha256=hashlib.sha256((D/'sites222.json').read_bytes()).hexdigest(),startup=dict(steps=409835,native_state=q,canonical_state=cq,head=h,one_cells=sorted(ones),all_other_cells=0,logical_registers=logical,physical_registers=physical,spares=[1]*167,extra_gap=117,used_native_rows=[list(k)+[v]for k,v in sorted(vis.items())]),scope='Literal table bijection and exact blank initialization only; source calculus and unbounded runtime are separate obligations.')
(D/'canonicalization.json').write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:v for k,v in r.items()if k not in('native_to_canonical','canonical_to_native','startup')},indent=2))

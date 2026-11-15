"""Check the finite inductive interval certificate; no source execution or sampling."""
from pathlib import Path
import json
B=Path(__file__).resolve().parent
D=json.loads((B/'abstract_regs.json').read_text())
I=json.loads((B/'baseline/source/pa194.instructions.json').read_text())
V={int(k):v for k,v in D['intervals'].items()}
K=3;INF=4
assert all(lo<=n and (hi==INF or n<=hi) for n,(lo,hi) in zip([2]+[0]*8,V[25]))
assert all(len(v)==9 and all(0<=a<=K and a<=b<=INF for a,b in v) for v in V.values())
checks=0
for pc,v in V.items():
 c=I[pc];successors=[]
 if c[0]=='inc':
  _,r,n=c;w=[x[:]for x in v];a,b=w[r];w[r]=[min(K,a+1),min(INF,b+1)];successors.append((n,w))
 elif c[0]=='dec':
  _,r,z,n=c;a,b=v[r]
  if a==0:
   w=[x[:]for x in v];w[r]=[0,0];successors.append((z,w))
  if b>0:
   w=[x[:]for x in v];w[r]=[max(0,a-1),INF if b==INF else b-1];successors.append((n,w))
 elif c[0]=='jump':successors.append((c[1],v))
 else:assert c==['halt']
 for n,w in successors:
  assert n in V,(pc,n)
  assert all(lo<=a and b<=hi for(a,b),(lo,hi)in zip(w,V[n])),(pc,n)
  checks+=1
result={'ok':True,'source_sites':len(I),'inhabited_abstract_sites':len(V),'initial_site':25,'initial_registers':[2]+[0]*8,'transfer_edges_checked':checks,'known_zero_decrement_sites':[pc for pc,v in V.items()if I[pc][0]=='dec' and v[I[pc][1]][1]==0],'unreachable_sites':[pc for pc in range(len(I))if pc not in V],'scope':'Inductive source-register interval invariant; not a physical-machine simulation or arithmetic calibration.'}
(B/'interval_certificate_check.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

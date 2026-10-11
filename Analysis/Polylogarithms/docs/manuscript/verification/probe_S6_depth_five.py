"""A precise depth-five double-shuffle escape probe for the S6 certificate.
This tests one finite input schema, not the entire extended relation space.
"""
from pathlib import Path
from fractions import Fraction as Q
from collections import defaultdict
from itertools import permutations,product
import hashlib,json,sys,time
sys.dont_write_bytecode=True
B=Path(__file__).resolve().parents[1];V=B/'verification'
C=B.parent/'reports/stieltjes-harmonic-resonance/continuations/exact-resonant-identities/certificates/cayley'
sys.path.insert(0,str(C/'code'))
import verify_complete_cayley as M
P,R=M.P,M.R
for name,digest in M.EXPECTED_SHA256.items():assert hashlib.sha256((C/name).read_bytes()).hexdigest()==digest
coords=[w for w in product(range(5),repeat=7) if P.admissible(w) and P.depth(w)<=4 and P.parity(w)]
data=json.loads((C/'data/separator.json').read_text());ell={coords[i]:c for i,c in data['functional']}
back={P.Z:{-1:1},P.X:{0:1,2:-1},P.Y:{1:1,3:-1},P.H:{1:1,3:1,2:-1},P.B:{2:1}}
def to_raw(w):
 out={():Q(1)}
 for a in w:out={u+(b,):c*d for u,c in out.items() for b,d in back[a].items()}
 return out
def adapted(poly):
 out=defaultdict(Q)
 for w,c in poly.items():
  for t,d in M.change_basis(w).items():out[t]+=c*d
 return {w:c for w,c in out.items() if c}
started=time.monotonic();records=[];escape=[]
words=sorted(set(permutations((P.Z,P.Z,P.X,P.X,P.X,P.Y))))
words=[w for w in words if P.admissible(w)]
for i,w in enumerate(words,1):
 u={ (0,):1,(2,):-1 };v=to_raw(w)
 row=R.plus(R.shpoly(u,v),R.product_poly(u,v),-1)
 assert all(len(t)==7 and t[0]!=0 and t[-1]!=-1 for t in row)
 a=adapted(row);proj=P.apply(P.projection,a)
 assert all(P.admissible(t) and len(t)==7 and P.parity(t) for t in proj)
 dep=max((P.depth(t) for t in proj),default=0)
 pairing=sum(c*ell.get(t,0) for t,c in proj.items())
 item=dict(input_adapted_word=list(w),input_depth_sum=5,raw_support=len(row),projected_support=len(proj),maximum_projected_depth=dep,bounded_space_member=dep<=4,zero_extended_pairing=str(pairing))
 item['projected_relation']=[dict(word=list(t),coefficient=str(c)) for t,c in sorted(proj.items())]
 if dep<=4 and pairing:
  item['bounded_pairing']=str(pairing);escape.append(item)
 records.append(item);print('Depth-five schema',i,'/',len(words),'projected depth',dep,'bounded escape',bool(dep<=4 and pairing),flush=True)
result=dict(status='PASS',schema='DS(X,v), X=C-B and v an admissible permutation of ZZXXXY; inputs have total depth five.',tested_inputs=len(words),bounded_projected_rows=sum(x['bounded_space_member'] for x in records),bounded_nonzero_pairings=len(escape),rows=records,elapsed_seconds=round(time.monotonic()-started,3),source_code_sha256={name:digest for name,digest in M.EXPECTED_SHA256.items()},scope='Each row is a linear combination of standard convergent or one-divergence double-shuffle rows, then projected by the proved full-Cayley retraction. A nonzero pairing is meaningful as a bounded-span escape only when the projected row lies in F4. Zero extension outside F4 is labeled only as a diagnostic. This finite schema does not prove S6, nonmembership in the full higher-depth family, or numerical period independence.')
(V/'S6-depth-five-escape-probe.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8');print('Finite probe complete:',len(words),'inputs;',len(escape),'bounded escapes')

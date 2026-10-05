from pathlib import Path
from itertools import permutations
from functools import lru_cache
import sympy as s
from sympy.polys.matrices import DomainMatrix
import json,hashlib,time
ROOT=Path(__file__).resolve().parent;SNAP=ROOT.parent/'audit_snapshot'
a,b,c,p=s.symbols('a b c p',positive=True);syms=(a,b,c,p)
@lru_cache(None)
def cnt(cols):
 return len({tuple(sorted(inj)) for inj in permutations(range(3),len(cols)) if all(mask>>i&1 for mask,i in zip(cols,inj))})
def dm(M):return DomainMatrix.from_Matrix(M).to_field().convert_to(s.QQ.frac_field(*syms))
records=[]
for path in sorted(SNAP.glob('BB_R_*.json')):
 start=time.time();d=json.loads(path.read_text());J,K=d['pair'];piv=d['pivots'];n=len(piv)
 E=p+a*K.bit_count()+b*J.bit_count()+c*(J|K).bit_count()+cnt((J,K))
 r=s.Matrix([p*S.bit_count()+a*cnt((K,S))+b*cnt((J,S))+c*cnt((J|K,S))+cnt((J,K,S)) for S in range(1,8)])
 h=s.Matrix(7,7,lambda i,j:p*cnt((i+1,j+1))+a*cnt((K,i+1,j+1))+b*cnt((J,i+1,j+1))+c*cnt((J|K,i+1,j+1)))
 H=3*r*r.T-4*E*h;H=H.extract(piv,piv);r=r.extract(piv,[0])
 inv=s.Matrix([[s.sympify(v,locals=dict(zip(('a','b','c','p'),syms))) for v in row] for row in d['inverse']])
 hd,iv,rd=dm(H),dm(inv),dm(r)
 if hd.matmul(iv)!=dm(s.eye(n)):raise RuntimeError(('inverse',J,K))
 ir=iv.matmul(rd);scalar=rd.transpose().matmul(ir).to_Matrix()[0]
 M=s.zeros(n+1);M[0,0]=(3-9*scalar)/(4*E);irm=ir.to_Matrix()
 for i in range(n):
  M[0,i+1]=M[i+1,0]=3*irm[i]
  for j in range(n):M[i+1,j+1]=-4*E*inv[i,j]
 T=s.eye(n+1)
 for i,k in enumerate(piv):T[i+1,0]=(k+1).bit_count()
 predicted=dm(T).transpose().matmul(dm(M)).matmul(dm(T))
 cache=json.loads((SNAP/f'BB_M_centered_{J}_{K}.json').read_text())
 if cache['pivots']!=piv:raise RuntimeError('pivot mismatch')
 D=s.sympify(cache['denominator'],locals=dict(zip(('a','b','c','p'),syms)))
 supplied=s.zeros(n+1)
 for i,j,terms in cache['entries']:
  v=sum(s.Rational(v)*s.prod(z**k for z,k in zip(syms,e)) for e,v in terms)/D
  supplied[i,j]=supplied[j,i]=v
 if predicted!=dm(supplied):raise RuntimeError(('centered kernel',J,K))
 records.append(dict(pair=[J,K],dimension=n,passed=True,seconds=time.time()-start,inverse_sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
 print(J,K,'PASS',round(time.time()-start,2),flush=True)
json.dump({'passed':True,'kernels':len(records),'records':records},open(ROOT/'kernel_results.json','w'),indent=2)

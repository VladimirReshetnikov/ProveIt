#!/usr/bin/env python3
"""Independent parent→88 ring field source review; no Lean."""
import hashlib,json,random,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary13-parent-to-88-ring-client-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'RingParentTo88.lean','a927b72a4751d3ad76cb83a7f3384949a8a6d5eb5e90e36c68bb860597b3583c').decode()
pin(A/'check_source.py','2068cbba39d7b2be5670f8e89b37828170cd9722460c20ad677248dad6f5c210')
receipt=pin(A/'observation.json','af4b9a12c0657740fb6c86bc5543ee890bbd840abb1fbb9cc10fe99bee6bf9c5')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary13-parent-to-88-ring-client-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='887f27f86f5fbc1873db222a9227632a18b0105d56e05854bfc3e7705a5300b4'
for name,ch,rh in (
 ('ordinary14-88-parent-ring-client-draft-independent','880c9b6e5b89a922d05f35414367af24a5e4d1dea0667479ce6fd7add019e43a','ee5684d0c6d91a32eb601dc8370b1195201e716a29cfeca7c8a5593ab5a4a848'),
 ('ordinary14-parent-to-88-first-cut-draft-independent','608ca58009404a3be7586a38c0867e7da63e0de6b9c6f8ed7660f1ed0b7ccc76','6c6a51f850d210f1c64b12fed05af2089e8803f216fb86937c69f1da70020b05')):
 p=D/'reviews'/name;pin(p/'check.py',ch);pin(p/'result.json',rh)
for f in ('![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,sigma,v 9,v 10,v 11,v 12,t]',
 'Ring88ToParentDraft.project (extend v sigma t) (v 8)=v',
 'Ring88ToParentDraft.main_eval p (extend v sigma t) (v 8)',
 'Ring88ToParentDraft.aux_eval p (extend v sigma t) (v 8)',
 'Ring88ToParentDraft.strong_eval p (extend v sigma t) (v 8)',
 'Ring88ToParentDraft.k w-sigma)+w 7*Ring88ToParentDraft.b p w'):
 assert f in s,f
parent=json.loads((D/'research/ordinary13-four-square88-30/candidate.json').read_bytes())
target=json.loads((D/'research/ordinary14-guarded-fold88-26/candidate.json').read_bytes())
def ev(g,vals,ports,mod):
 v=dict(zip(g['witnesses'],vals));v.update(dict(zip(g['fixed_numerals'],ports)))
 for name,op,a,b in g['source']:
  a=v[a] if isinstance(a,str) else a;b=v[b] if isinstance(b,str) else b
  v[name]=(a+b if op=='+' else a-b if op=='-' else a*b)%mod
 return v
rng=random.Random(131488)
for mod in (12,97):
 for _ in range(100):
  v=[rng.randrange(mod) for _ in range(13)];p=[rng.randrange(mod) for _ in range(4)]
  sigma=rng.randrange(mod);t=rng.randrange(mod);w=v[:8]+[sigma]+v[9:]+[t]
  a=ev(parent,v,p,mod);z=ev(target,w,p,mod)
  assert all(a[x]==z[x] for x in ('A1','Fa','g72'))
  b=v[0]*p[0];q=1+b;M=q**3*b;k=v[9]+v[10];ell=v[6]*v[7]*v[7]*k
  Z=M*(ell+k-sigma)+v[7]*b
  assert z['A0']==(Z*Z-M*M*(1+ell*(ell+k)))%mod
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'parent-to-88 ring field source review; no Lean','finite_ring_controls':200,'prior_component_reviews':'pinned, not rerun'},sort_keys=True,indent=2))

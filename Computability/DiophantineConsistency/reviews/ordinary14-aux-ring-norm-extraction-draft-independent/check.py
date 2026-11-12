#!/usr/bin/env python3
"""Independent source, exact-algebra and finite-sign review; no Lean."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

D = Path(__file__).resolve().parents[2]
A = D / 'research/ordinary14-aux-ring-norm-extraction-draft'
R = D / 'reviews/ordinary14-aux-norms-to-bounds-draft-independent'

def sha(data): return hashlib.sha256(data).hexdigest()
def pinned(path, expected):
    data = path.read_bytes()
    assert sha(data) == expected, str(path)
    return data

source = pinned(A / 'RingNormExtraction.lean', '771cc1bf65a1d0e2b195627a45a4d152671ed0e86dbf12516855bfe8f1c11216').decode()
readme = (A / 'README.md').read_bytes()
tail = (b'\nIndependent source review is recorded in\n'
        b'`../../reviews/ordinary14-aux-ring-norm-extraction-draft-independent/`.\n')
assert readme.endswith(tail)
assert sha(readme[:-len(tail)]) == '51f7a6100d70da154ef3f937554f07f9c7f467b1e5ba3bbf0f27720170760700'
model = pinned(D / 'Lean/DiophantineConsistency/ModelDifferenceRing.lean',
               '5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998').decode()
scaled = pinned(D / 'Lean/DiophantineConsistency/ArithmeticAdaptiveQuotients2011.lean',
                '40070b23fceee62a689a1002f97f6f612057634b5bd8472949f0d2dcab136884').decode()
compose = pinned(D / 'research/ordinary14-aux-norms-to-bounds-draft/NormsToBounds.lean',
                 'c93161930052792db7b9ebb08f04f897e70d70fa84d390926521b7b4e28a70f8').decode()
for text in ('theorem root_of_scaled_ring_square', '(hU : 0<U)',
             'nonneg_or_nonpos Z', 'scaled_quotient U z n hU hsq',
             'theorem first_norm_of_ring_residual', 'theorem strong_norm_of_ring_residual',
             'theorem bounds_of_direct_field_residuals', '(hDeltaDef :',
             '(hQ : Q=(ι i*ι c*ι c)*(ι i*ι c*ι c))',
             '(hz : z+ι c=(ι f*ι f)*t)', 'aux_bounds_of_natural_norms'):
    assert text in source, text
assert 'theorem nonneg_or_nonpos (x : DiffRing V) : ∃' not in model  # The actual interface has an Or.
assert 'theorem nonneg_or_nonpos (x : DiffRing V) : (∃ c, x = ι c) ∨ ∃ c, x = -ι c' in model
assert 'theorem ι_injective : Function.Injective (ι : V →+* DiffRing V)' in model
assert 'theorem scaled_quotient (m z n : V) (hm : 0<m) (h : z*z=m*m*n)' in scaled
assert 'theorem aux_bounds_of_natural_norms' in compose

def const(n): return {(): n} if n else {}
def var(name): return {(name,): 1}
def add(a,b,sign=1):
    out=dict(a)
    for key,val in b.items(): out[key]=out.get(key,0)+sign*val
    return {key:val for key,val in out.items() if val}
def mul(a,b):
    out={}
    for ka,va in a.items():
        for kb,vb in b.items():
            key=tuple(sorted(ka+kb))
            out[key]=out.get(key,0)+va*vb
    return {key:val for key,val in out.items() if val}
x,y,k,i,c,delta,f=map(var,('X','Y','k','i','c','Delta','f'))
m=mul(mul(x,y),y)
ell=mul(m,k)
assert add(const(1),mul(ell,add(ell,k))) == add(const(1),mul(mul(m,add(m,const(1))),mul(k,k)))
I=mul(mul(i,c),c)
residual=add(mul(I,I),mul(delta,add(mul(f,f),const(1),-1)),-1)
assert residual == add(add(mul(I,I),delta),mul(delta,mul(f,f)),-1)

sign_cases = {'negative':0,'zero':0,'positive':0}
for scale in range(1, 16):
    for root in range(0, 31):
        for sign in (-1,1):
            z=sign*scale*root
            n=root*root
            assert z*z==scale*scale*n and abs(z)==scale*root
            sign_cases['negative' if z<0 else 'positive' if z>0 else 'zero'] += 1
assert all(sign_cases.values())
# A zero scale makes Z²=U²n hold for nonsquare n without supplying a root.
assert 0*0 == 0*0*2 and all(d*d != 2 for d in range(4))

def replay(path, receipt):
    run=subprocess.run([sys.executable,'-I','-S','-B',str(path)],cwd=D,
                       stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=30,check=True)
    assert not run.stderr and run.stdout==receipt.read_bytes()

replay(A/'check_source.py',A/'observation.json')
replay(R/'check.py',R/'result.json')
print(json.dumps({'scope':'source and exact finite controls only; no Lean or model theorem',
                  'author_readme_prelink_sha256':sha(readme[:-len(tail)]),
                  'exact_norm_identities':True,'finite_sign_cases':sign_cases,
                  'zero_scale_boundary':True,'composition_review_replayed':True},sort_keys=True,indent=2))

#!/usr/bin/env python3
"""Independent ring-algebra and cited-interface inspection; no Lean."""
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2]
def pin(path,h):
 b=(D/path).read_bytes();assert hashlib.sha256(b).hexdigest()==h,path;return b.decode()
s=pin('research/ordinary14-natural79-w-model-route/ForcedWDivisibility.lean','111f5a6da543baf6f08b3b1c6e5e8371cfb222197ba4566b8693598edffb6833')
sq=pin('Lean/DiophantineConsistency/ArithmeticSquareDivisibility.lean','f775c2050a794b1ea026cdec0950e42528260fa1d75a03f1ef625f258670e660')
q=pin('Lean/DiophantineConsistency/ArithmeticAdaptiveQuotients2011.lean','40070b23fceee62a689a1002f97f6f612057634b5bd8472949f0d2dcab136884')
mag=pin('Lean/DiophantineConsistency/Compact44/ReducedNormSigned.lean','c01a13fd7f48c5abeb8a6741e19adad7b9d848fc57d51057c8bbb4694139674c')
reflect=pin('Lean/DiophantineConsistency/BFS943/Direct80NaturalProjection.lean','85e1fdcee61eeea97af1dead36de5f6593a94fb7c1f63678922ef0909b128028')
units=pin('Lean/DiophantineConsistency/ArithmeticSignedPairs.lean','ecad260baefecc05bab664a976015d7a76228583c7ec25bcc7536890ef58274d')
old=pin('research/ordinary14-74-ownzero-product-draft/OwnZeroProduct74.lean','26404a26b78b3099ddaa407d2eed829d884568821e08a5c7780a1e0ac167a1db')
g=json.loads(pin('research/ordinary14-natural-forced-w79/candidate.json','0d047283e1aed25040871e7d0b797ac168e5f80c596d4551fec916d48fe84cb5'));rows={n:[op,x,y] for n,op,x,y in g['source']}
assert len(rows)==79 and rows['X']==['*','q','n_w'] and rows['E']==['*','X','Y'] and rows['ell']==['*','E','kY']
assert rows['g38']==['*','n_r','n_r'] and rows['g40']==['*','ell','g30'] and rows['F0']==['-','g38','g40']
assert '(hJ : 0<v 0) (hw : 0<v 6) (hs : 0<v 7)' in old
assert 'theorem dvd_of_square_dvd (m z : V) (hm : 0<m) (h : m*m ∣ z*z) : m∣z' in sq
assert 'theorem scaled_quotient (m z n : V)' in q
assert '∃ a : V, (x=ι a ∨ x= -ι a) ∧ x*x=ι (a*a)' in mag
assert 'theorem natural_dvd_of_signed (a b : V) (hd : (ι a : DiffRing V)∣ι b) : a∣b' in reflect
assert 'theorem product5_magnitudes' in units and 'theorem product5_positive' in units
assert '(hdiv : H ∣ U*(d-a*c))' in s and '(hnorm : d*d=1+(a*a+H)*c*c)' in s
assert '⟨z*(d+a*c)-U*c*c,?_⟩' in s and '⟨q*q-4*z,?_⟩' in s
# Formal polynomial check of the identities used to obtain both witnesses.
def var(x):return {(x,):1}
def const(x):return {():x}
def add(a,b):
 r=dict(a)
 for k,v in b.items():r[k]=r.get(k,0)+v
 return {k:v for k,v in r.items() if v}
def neg(a):return {k:-v for k,v in a.items()}
def sub(a,b):return add(a,neg(b))
def mul(a,b):
 r={}
 for x,u in a.items():
  for y,v in b.items():
   k=tuple(sorted(x+y));r[k]=r.get(k,0)+u*v
 return {k:v for k,v in r.items() if v}
H,U,d,a,c,z,q,Y=map(var,('H','U','d','a','c','z','q','Y'));one=const(1);three=const(3);four=const(4)
# U*(norm-1) equals the algebraic product minus U*H*c².
left=sub(mul(mul(U,sub(d,mul(a,c))),add(d,mul(a,c))),mul(mul(U,H),mul(c,c)))
right=mul(U,sub(mul(d,d),mul(add(mul(a,a),H),mul(c,c))))
assert left==right
# H=4Y+3, U=Yq² imply Hq²-4U=3q².
assert sub(mul(add(mul(four,Y),three),mul(q,q)),mul(four,mul(Y,mul(q,q))))==mul(three,mul(q,q))
print(json.dumps({'scope':'source signatures and universal ring identities, not Lean proof or model theorem','pinned_sources':8,'ring_identities':2,'positive_w_required_by_74_extractor':True},sort_keys=True,indent=2))

#!/usr/bin/env python3
"""Pin the model-divisibility interfaces; no Lean or graph proof."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;D=P.parents[1];L=D/'Lean/DiophantineConsistency'
pins={
 P/'ForcedWDivisibility.lean':'111f5a6da543baf6f08b3b1c6e5e8371cfb222197ba4566b8693598edffb6833',
 L/'ArithmeticSquareDivisibility.lean':'f775c2050a794b1ea026cdec0950e42528260fa1d75a03f1ef625f258670e660',
 L/'ArithmeticAdaptiveQuotients2011.lean':'40070b23fceee62a689a1002f97f6f612057634b5bd8472949f0d2dcab136884',
 L/'Compact44/ReducedNormSigned.lean':'c01a13fd7f48c5abeb8a6741e19adad7b9d848fc57d51057c8bbb4694139674c',
 L/'BFS943/Direct80NaturalProjection.lean':'85e1fdcee61eeea97af1dead36de5f6593a94fb7c1f63678922ef0909b128028',
 L/'ArithmeticSignedPairs.lean':'ecad260baefecc05bab664a976015d7a76228583c7ec25bcc7536890ef58274d',
 L/'ModelDifferenceRing.lean':'5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998',
 D/'research/ordinary14-74-ownzero-product-draft/OwnZeroProduct74.lean':'26404a26b78b3099ddaa407d2eed829d884568821e08a5c7780a1e0ac167a1db',
 D/'research/ordinary14-74-first-factor-client-draft/FirstFactor74.lean':'fca24f5e8e3be0743e3423f66573e099a211f3c2cfc973d69f77c0a2ff8d62f4',
 D/'research/ordinary14-74-factor-residues-draft/FactorResidues74.lean':'368e6e5f3db5693db859fdc85a9441f0d6378969563eec289c2c121e6b4b1d60',
 D/'research/ordinary14-natural-forced-w79/candidate.json':'0d047283e1aed25040871e7d0b797ac168e5f80c596d4551fec916d48fe84cb5',
}
src={}
for p,h in pins.items():
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,str(p);src[p.name]=b.decode()
checks={
 'ForcedWDivisibility.lean':['theorem divisor_of_main_norm','theorem divisor_of_three_square',
   '(hdiv : H ∣ U*(d-a*c))','(hnorm : d*d=1+(a*a+H)*c*c)'],
 'ArithmeticSquareDivisibility.lean':['theorem dvd_of_square_dvd (m z : V)','No prime factorization or standardness premise'],
 'ArithmeticAdaptiveQuotients2011.lean':['theorem scaled_quotient (m z n : V)'],
 'ReducedNormSigned.lean':['theorem natural_magnitude_square (x : DiffRing V)'],
 'Direct80NaturalProjection.lean':['theorem natural_dvd_of_signed (a b : V)'],
 'ArithmeticSignedPairs.lean':['theorem product5_magnitudes','theorem product5_positive'],
 'OwnZeroProduct74.lean':['theorem product_of_zero','theorem factor_units_of_zero',
   '(hJ : 0<v 0) (hw : 0<v 6) (hs : 0<v 7)'],
 'FirstFactor74.lean':['theorem first_eval','theorem m_at_least_two',
   '(hb : 0<beta) (hJ : 0<v 0) (hw : 0<v 6) (hs : 0<v 7) : 2≤m beta v'],
 'FactorResidues74.lean':['theorem restricted_residues'],
 'ModelDifferenceRing.lean':['theorem internalZero_iff','theorem one_le_of_pos'],
}
for f,needles in checks.items():
 for x in needles:assert x in src[f],(f,x)
assert 'sorry' not in src['ForcedWDivisibility.lean'] and 'admit' not in src['ForcedWDivisibility.lean']
graph=json.loads(src['candidate.json']);assert graph['operations']==len(graph['source'])==79
nodes={row[0]:row[1:] for row in graph['source']}
shape={'q':['+',1,'qm'],'X':['*','q','n_w'],'q2':['*','q','q'],'q3':['*','q','q2'],
 'Y':['*','q3','s'],'U':['*','Y','q2'],'a':['+','E','Y'],'E':['*','X','Y'],
 'H':['+',3,'g15'],'g15':['*',4,'a'],'g17':['*','a','a'],
 'Delta':['+','H','g17'],'ell':['*','E','kY'],'g38':['*','n_r','n_r'],
 'g40':['*','ell','g30'],'F0':['-','g38','g40'],
 'Dstar':['+','g58','g59'],'g58':['*','U','b0'],'g59':['*','H','shift'],
 'b0':['+','X','g19'],'g19':['*','a','c'],
 'A1':['-','g61','g65'],'g61':['*','Dstar','Dstar'],
 'g62':['*','U','U'],'g63':['*','Delta','c2'],'g64':['+',1,'g63'],
 'g65':['*','g62','g64'],'F1':['+',1,'A1']}
assert all(nodes[n]==row for n,row in shape.items())
# Exact sparse-polynomial checks of the ring rearrangements in the source.
def var(name):return {(name,):1}
def one():return {():1}
def add(a,b):
 out=dict(a)
 for k,v in b.items():out[k]=out.get(k,0)+v
 return {k:v for k,v in out.items() if v}
def neg(a):return {k:-v for k,v in a.items()}
def sub(a,b):return add(a,neg(b))
def mul(a,b):
 out={}
 for ka,va in a.items():
  for kb,vb in b.items():
   k=tuple(sorted(ka+kb));out[k]=out.get(k,0)+va*vb
 return {k:v for k,v in out.items() if v}
def scale(n,a):return {k:n*v for k,v in a.items() if n*v}
H,U,d,a,c,q,Y=map(var,('H','U','d','a','c','q','Y'))
dc=mul(a,c); cc=mul(c,c); qq=mul(q,q)
left=sub(mul(mul(U,sub(d,dc)),add(d,dc)),mul(mul(U,H),cc))
right=mul(U,sub(mul(d,d),mul(add(mul(a,a),H),cc)))
assert left==right
assert sub(mul(add(scale(4,Y),scale(3,one())),qq),scale(4,mul(Y,qq)))==scale(3,qq)
for y in range(1,100):
 H=4*y+3;a=y;c=2*(a+2);d=2*(a+2)**2-1
 assert d*d==1+(a*a+H)*c*c
 U=H*3;z=3*(d-a*c);w=z*(d+a*c)-U*c*c
 assert H*w==U
print(json.dumps({'scope':'pinned source interfaces and finite ring controls only',
                  'pinned_sources':len(pins),'graph_shape_rows':len(shape),'exact_polynomial_identities':2,'algebra_controls':99,
                  'model_square_divisibility_source_statement_inspected':True,
                  'axiom_prints_not_executed':2,'no_lean_or_ipra_claim':True},sort_keys=True,indent=2))

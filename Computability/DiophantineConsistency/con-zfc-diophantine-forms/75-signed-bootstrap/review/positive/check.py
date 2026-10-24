#!/usr/bin/env python3
"""Independent symbolic projection and carrier-interface audit, not semantics."""
import json, hashlib, math
from pathlib import Path
import sympy as s
ROOT=Path(__file__).resolve().parents[2]
OUT=Path(__file__).resolve().parent

def require(x,msg):
    if not x: raise RuntimeError(msg)
def equal(a,b,msg): require(s.expand(a-b)==0,msg)
parent=json.loads((ROOT/'mixed_source/parent_source.json').read_text())
names=parent['sparse_term_coordinate_order']; syms=s.symbols(' '.join(names)); ds=dict(zip(names,syms))
original=[s.Poly.from_dict({tuple(t['powers']):t['coefficient'] for t in e['terms']},syms).as_expr() for e in parent['equations']]
results=[]
for n,d,rows,terms in [(21,4,12,100),(24,4,15,89),(26,3,17,85)]:
    p=ROOT/f'mixed_source/source{n}.json'; data=json.loads(p.read_text())
    require(data['source_sha256']==hashlib.sha256((ROOT/'mixed_source/parent_source.json').read_bytes()).hexdigest(),'source hash')
    defs={ds[k]:s.sympify(v,locals=ds) for k,v in data['definitions'].items()}; vs=[ds[k] for k in data['variables']]
    require(len(vs)==n and len(set(vs))==n,'variables')
    require(set(vs).isdisjoint(defs) and set(vs)|set(defs)==set(syms[:31]),'partition')
    require(all(not (v.free_symbols & set(defs)) for v in defs.values()),'dependency closure')
    reduced={e['old_row']:s.sympify(e['residual'],locals=ds) for e in data['equations']}
    for j,r in enumerate(original,1): equal(r.subs(defs, simultaneous=True),reduced.get(j,0),f'projection row {j}')
    require(len(reduced)==rows,'rows')
    degrees=[]; count=0
    for e in data['equations']:
        sparse=sum(s.sympify(t['coefficient'],locals=ds)*s.prod(v**a for v,a in zip(vs,t['powers'])) for t in e['terms'])
        equal(sparse,reduced[e['old_row']],'sparse identity')
        poly=s.Poly(sparse,*vs); degrees.append(poly.total_degree()); count+=len(poly.terms())
    require(max(degrees)==d and count==terms,'metrics')
    # A perturbation cannot pass any all-value reconstruction identity.
    first=next(iter(reduced)); require(s.expand(original[first-1].subs(defs, simultaneous=True)-reduced[first]-1)!=0,'negative control')
    results.append({'variables':n,'residuals':rows,'maximum_residual_degree':d,'sos_degree':2*d,'source_support_terms':count})
# Exact positive reconstruction certificate from the retained row consequences.
E,eta,zeta,j,h,s0,N=s.symbols('E eta zeta j h s N',positive=True,integer=True)
k=eta+zeta; c=k*s0*N+eta
P=E*(c-eta)+k; V=j*c+h*E-k+1
# Positive rewrite for V, using s,N,j >=1.
equal(V,(j-1)*c+h*E+k*(s0*N-1)+eta+1,'positive V decomposition')
equal(P,E*k*s0*N+k,'positive P decomposition')
# Carrier equation: exact recovery, no coprimality omitted.
q,X,Y,R,gamma,a,c,H=s.symbols('q X Y R gamma a c H',integer=True)
r0=s.symbols('r0',integer=True); K=4*q*Y; U=q*K
Dstar=U*(X+a*c)+H*(U*gamma+K*X-r0)
equal(Dstar,U*(X+a*c+H*(gamma+X/q-r0/U)),'carrier recovery')
# gcd and strict absorber bounds sampled only as supplemental arithmetic tests.
cases=0
for q0 in range(17,101,3): # q=2 modulo3
    for x0 in range(1,7):
      for t in range(1,5):
        y0=t*q0**3; h0=4*y0*(x0+1)+3; k0=4*q0*y0
        g=math.gcd(k0,h0)
        require(g==math.gcd(y0,3) and g<=3,'gcd identity')
        require(k0//g>q0**4-1,'absorber bound')
        require((4*x0*y0*y0)%(4*q0*q0*y0)==0,'quotient integral')
        cases+=1
pins={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [ROOT/'low_degree/PROOF.md',ROOT/'low_degree/COEFFICIENT_BINDING.json',ROOT/'mixed_source/COEFFICIENT_BINDING.json',ROOT/'low_degree/p13_degree30.json',ROOT/'low_degree/p12_product_split2.json',ROOT/'mixed_source/PROOF.md',ROOT/'mixed_source/parent_source.json',*[ROOT/f'mixed_source/source{n}.json' for n in (21,24,26)]]}
receipt={'status':'passed','scope':'Exact finite algebra and source projection; mathematical proof separately reviewed; not a kernel or consistency check.','projections':results,'supplementary_gcd_cases':cases,'corruption_controls':3,'pins':pins}
(OUT/'CHECK.json').write_text(json.dumps(receipt,indent=2)+'\n'); print(json.dumps(receipt,indent=2))

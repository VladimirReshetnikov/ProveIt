#!/usr/bin/env python3
"""Eq -> two-sided Rel indiscernibility using primitive symmetry, not rho7."""
from pathlib import Path
import json
from equality_certificates import P,I,Q,N,Eq,F,k,mp,abst,hyp,mono,emono,export,assumptions,rho1
R=lambda a,b:('rel',a,b)
And=lambda a,b:N(I(a,N(b)))
code=lambda f:('native_code',f)

def sym(a,b):return P('Sym',I(Eq(a,b),Eq(b,a)))
def right_cong(a,b,z):return P('rho3',I(Eq(a,b),I(R(z,a),R(z,b))))
def left_cong(a,b,z):return P('rho5',I(Eq(a,b),I(R(a,z),R(b,z))))
def comp(p,q):
 a,b=p.form[1:]
 if q.form[1]!=b:raise ValueError('composition')
 return abst(a,mp(q,mp(p,hyp(a))))
def conjunction(p,q):
 # p and q may have common open hypotheses; negative conjunction introduction.
 return abst(I(p.form,N(q.form)),mp(mp(hyp(I(p.form,N(q.form))),p),q))
def E(a,b,z):
 inward=Q(z,And(I(R(z,a),R(z,b)),I(R(z,b),R(z,a))))
 outward=Q(z,And(I(R(a,z),R(b,z)),I(R(b,z),R(a,z))))
 return And(inward,outward)
def certificate(kind):
 a,b='a','b';e=Eq(a,b)
 if kind=='canonical':
  z=('weq',a,b);v=P('V_eq',I(e,Q(z,e)))
 else:
  z=code(I(e,('meta','B')));v=P('PV',I(e,Q(z,e)))
 def both(fwd,rev):
  p=abst(e,conjunction(mp(fwd,hyp(e)),mp(rev,hyp(e))))
  return comp(v,mono(z,p))
 inward=both(right_cong(a,b,z),comp(sym(a,b),right_cong(b,a,z)))
 outward=both(left_cong(a,b,z),comp(sym(a,b),left_cong(b,a,z)))
 bridge=abst(e,conjunction(mp(inward,hyp(e)),mp(outward,hyp(e))))
 if bridge.form!=I(e,E(a,b,z)):raise ValueError('wrong E shape')
 witness=mp(emono(a,bridge),rho1(a,b))
 return bridge,witness
roots={}
for kind in ('canonical','projection'):
 bridge,witness=certificate(kind)
 roots[kind+'_Eq_to_E']=bridge
 roots[kind+'_exists_E']=witness
for p in roots.values():
 if assumptions(p):raise ValueError('open root')
D=export(roots)
D['scope']='Primitive Sym replaces rho7. E is exactly the requested pair of universally quantified bidirectional Rel conditions, with negative conjunction. Uses rho1,rho2,rho3,rho5 and V_eq or PV; no Eq reflexivity, transitivity, old vacuity, DNE, CP/GIC, or alpha conversion.'
Path(__file__).with_name('eq_to_indiscernibility_proofs.json').write_text(json.dumps(D,separators=(',',':'))+'\n')
print({'nodes':len(D['proof_nodes']),'formulas':len(D['formulas'])})

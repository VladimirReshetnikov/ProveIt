#!/usr/bin/env python3
"""Proof-local checks for arbitrary safe-off-diagonal equality helpers.
Generator utilities are imported; verification below independently checks
all actual node formulas and GEN closure. Safe under python -O.
"""
from pathlib import Path
from itertools import product
import json
from equality_certificates import P,I,Q,N,Ex,Eq,F,k,mp,abst,hyp,mono,emono,rho1,rho2,rho6,rho7,gen,ident,export,assumptions
R=lambda a,b:('rel',a,b)
And=lambda a,b:N(I(a,N(b)))
pair=lambda a,b:(a+b)*(a+b+1)//2+b
builders={
 'weq_ab':lambda a,b:4*pair(a,b)+3,
 'wrel_ab':lambda a,b:4*pair(a,b)+1,
 'wrel_ba':lambda a,b:4*pair(b,a)+1,
 'wall_ab':lambda a,b:4*pair(a,b)+2,
 'wall_ba':lambda a,b:4*pair(b,a)+2,
 'weq_ba':lambda a,b:4*pair(b,a)+3,
 'wim_ab':lambda a,b:4*pair(a,b),
 'wim_ba':lambda a,b:4*pair(b,a),
}
def need(v,m):
 if not v:raise ValueError(m)
def conj(p,q):return abst(I(p.form,N(q.form)),mp(mp(hyp(I(p.form,N(q.form))),p),q))
def comp(p,q):
 a,b=p.form[1:];need(q.form[1]==b,'bad composition')
 return abst(a,mp(q,mp(p,hyp(a))))
def E(a,b,z):
 return And(Q(z,And(I(R(z,a),R(z,b)),I(R(z,b),R(z,a)))),Q(z,And(I(R(a,z),R(b,z)),I(R(b,z),R(a,z)))))
def helper(a,b,kappa):
 e=Eq(a,b);return P('KAPPA',I(e,Q(kappa(a,b),e)))
def refl(x,kappa):
 z=kappa(x,x);d=Eq(z,x);e=Eq(x,x)
 d_e=abst(d,mp(mp(rho7(x,x,z),hyp(d)),hyp(d)))
 ex_e=mp(emono(z,d_e),rho1(z,x))
 ex_qe=mp(emono(z,helper(x,x,kappa)),ex_e)
 return mp(rho6(z,e),ex_qe)
def sym(x,y,kappa):
 e=Eq(x,y)
 return abst(e,mp(mp(rho7(y,x,x),hyp(e)),refl(x,kappa)))
def trans(x,y,z,kappa):
 xy,yz=Eq(x,y),Eq(y,z)
 return abst(xy,abst(yz,mp(mp(rho7(x,z,y),mp(sym(x,y,kappa),hyp(xy))),hyp(yz))))
def bridge(a,b,kappa):
 z=kappa(a,b);need(a!=b and z not in(a,b),'only safe off-diagonal bridge');e=Eq(a,b)
 sym_ab=P('Sym',I(e,Eq(b,a)))
 def right(a,b):return P('rho3',I(Eq(a,b),I(R(z,a),R(z,b))))
 def left(a,b):return P('rho5',I(Eq(a,b),I(R(a,z),R(b,z))))
 out=[]
 for congr in (right,left):
  p=abst(e,conj(mp(congr(a,b),hyp(e)),mp(comp(sym_ab,congr(b,a)),hyp(e))))
  out.append(comp(helper(a,b,kappa),mono(z,p)))
 p=abst(e,conj(mp(out[0],hyp(e)),mp(out[1],hyp(e))))
 need(p.form==I(e,E(a,b,z)),'bridge shape')
 return p,mp(emono(a,p),rho1(a,b))
def diagonal(x):
 z=builders['weq_ab'](x,x)
 l=gen(z,conj(ident(R(z,x)),ident(R(z,x))))
 r=gen(z,conj(ident(R(x,z)),ident(R(x,z))))
 theorem=conj(l,r);need(theorem.form==E(x,x,z),'diagonal shape')
 bridge=mp(k(theorem.form,Eq(x,x)),theorem)
 return theorem,bridge,mp(emono(x,bridge),rho1(x,x))
def verify(data,kappa,expected):
 fs=data['formulas'];nodes=data['proof_nodes'];opens=[];rules={}
 for ix,p in enumerate(nodes):
  r=p['rule'];f=fs[p['formula']];ar=p['args'];deps=frozenset();rules[r]=rules.get(r,0)+1
  if r=='K':need(f==I(f[1],I(f[2][1],f[1])),(ix,r))
  elif r=='S':
   a=f[1][1];b=f[1][2][1];c=f[1][2][2];need(f==I(I(a,I(b,c)),I(I(a,b),I(a,c))),(ix,r))
  elif r=='MP':
   l,h=ar;need(l<ix and h<ix,'acyclic MP');need(fs[nodes[l]['formula']]==I(fs[nodes[h]['formula']],f),(ix,r));deps=opens[l]|opens[h]
  elif r=='GEN':
   i,h=ar;need(h<ix,'acyclic GEN');need(not opens[h],'GEN with assumptions');need(f==Q(i,fs[nodes[h]['formula']]),(ix,r))
  elif r=='rho1':
   i=f[1][1];e=f[1][2][1];need(e[0]=='eq' and e[1]==i and f==Ex(i,e),(ix,r))
  elif r=='rho2':
   i=f[1][1];a,b=f[1][2][1:];need(f==I(Q(i,I(a,b)),I(Q(i,a),Q(i,b))),(ix,r))
  elif r=='rho6':
   i=f[1][1][1];a=f[2];need(f==I(Ex(i,Q(i,a)),a),(ix,r))
  elif r=='rho7':
   c,a=f[1][1:];cc,b=f[2][1][1:];need(c==cc and f==I(Eq(c,a),I(Eq(c,b),Eq(a,b))),(ix,r))
  elif r=='Sym':
   a,b=f[1][1:];need(f==I(Eq(a,b),Eq(b,a)),(ix,r))
  elif r=='rho3':
   a,b=f[1][1:];z=f[2][1][1];need(f==I(Eq(a,b),I(R(z,a),R(z,b))),(ix,r))
  elif r=='rho5':
   a,b=f[1][1:];z=f[2][1][2];need(f==I(Eq(a,b),I(R(a,z),R(b,z))),(ix,r))
  elif r=='KAPPA':
   a,b=f[1][1:];need(f==I(Eq(a,b),Q(kappa(a,b),Eq(a,b))),(ix,r))
  elif r=='HYP':deps=frozenset((f,))
  else:raise ValueError(('unknown rule',r))
  opens.append(deps)
 need(set(data['roots'])==set(expected),'wrong root names')
 for name,root in data['roots'].items():
  need(not opens[root],('open root',name));need(fs[nodes[root]['formula']]==expected[name],('wrong root',name))
 return dict(nodes=len(nodes),roots=len(expected),rules=rules)
reports={}
for name,kappa in builders.items():
 roots={};expected={}
 for x in (0,1,2,999):
  roots[f'refl_{x}']=refl(x,kappa);expected[f'refl_{x}']=Eq(x,x)
  roots[f'sym_{x}']=sym(x,0,kappa);expected[f'sym_{x}']=I(Eq(x,0),Eq(0,x))
  roots[f'trans_{x}']=trans(x,0,1,kappa);expected[f'trans_{x}']=I(Eq(x,0),I(Eq(0,1),Eq(x,1)))
 for a,b in ((0,1),(1,0),(1,2),(999,0)):
  p,q=bridge(a,b,kappa);z=kappa(a,b)
  roots[f'bridge_{a}_{b}']=p;expected[f'bridge_{a}_{b}']=I(Eq(a,b),E(a,b,z))
  roots[f'exists_{a}_{b}']=q;expected[f'exists_{a}_{b}']=Ex(a,E(a,b,z))
 reports[name]=verify(export(roots),kappa,expected)
 collisions=[]
 for a,b in product(range(64),repeat=2):
  z=kappa(a,b)
  need(a==b or z not in(a,b),('unsafe off-diagonal',name,a,b,z))
  if z in(a,b):collisions.append([a,b,z])
 reports[name]['collisions_below_64']=collisions
roots={};expected={}
for x in (0,1,999):
 p,q,r=diagonal(x);e=E(x,x,builders['weq_ab'](x,x))
 for tag,pf,formula in (('refl',p,e),('bridge',q,I(Eq(x,x),e)),('exists',r,Ex(x,e))):
  roots[f'{tag}_{x}']=pf;expected[f'{tag}_{x}']=formula
reports['diagonal_without_helpers']=verify(export(roots),lambda a,b:0,expected)
reports['valid']=True
reports['total_closed_roots']=sum(v['roots'] for v in reports.values() if isinstance(v,dict))
reports['total_nodes_replayed']=sum(v['nodes'] for v in reports.values() if isinstance(v,dict))
reports['scope']='Finite independent local-rule replay supplementing general_kappa_equality_helper.md. Diagonal fixed-E proofs use no helper, primitive equality fact, membership vacuity or classical tautology leaf. Every implication-builder zero collision is included literally.'
Path(__file__).with_name('general_kappa_results.json').write_text(json.dumps(reports,indent=2)+'\n')
print(json.dumps(reports,indent=2))

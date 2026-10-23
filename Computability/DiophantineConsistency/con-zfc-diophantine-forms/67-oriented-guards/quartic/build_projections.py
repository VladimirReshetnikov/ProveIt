#!/usr/bin/env python3
"""Exact monic coordinate elimination over Z; no division or sign conditions."""
from pathlib import Path
import json,hashlib
import sympy as s
R=Path(__file__).resolve().parent
p=json.loads((R/'quartic42.json').read_text());vs=p['variables'];fixed=p['fixed_numerals'];sym={x:s.Symbol(x) for x in vs+fixed};rows=[s.sympify(x,locals=sym) for x in p['residuals']]
def req(v,m):
 if not v:raise ValueError(m)
# Every defining residual has coefficient+1 in the variable eliminated.
definitions={'L':(0,'(beta*J+1)**2-1'),'N':(1,'(beta*J+1)*(L+1)'), 'X':(2,'(beta*J+1)*w'),'E':(3,'a-(2*v_scale+1)*N'), 'P':(6,'E*(c-eta)+eta+zeta'),'D':(8,'X+a*c+(4*a+3)*gamma'),'Delta':(9,'a**2+4*a+3'),'C2':(10,'c**2'),'F2':(14,'f**2'),'g':(17,'y**2-V**2'),'I':(18,'(2*r+1)*C2'),'Baux':(19,'I**2'),'w':(22,'4*u**2')}
variants=[('sextic36',['w','C2','F2','Baux','L','E'],6,('I',4,'g',2)),('octic32',['w','X','C2','Delta','F2','Baux','g','L','N','P'],8,('I',4,'V',4))]
receipts=[]
for label,eliminated,degree,witness in variants:
 subs={};visiting=set()
 def expand(name):
  if sym[name] in subs:return subs[sym[name]]
  req(name not in visiting,'cyclic elimination');visiting.add(name)
  idx,expr=definitions[name];e=s.sympify(expr,locals=sym)
  req(s.expand(rows[idx]-(sym[name]-e))==0 or s.expand(rows[idx]+(sym[name]-e))==0,'exact monic definition '+name)
  for n in eliminated:
   if sym[n] in e.free_symbols:e=e.subs(sym[n],expand(n))
  e=s.expand(e);subs[sym[name]]=e;visiting.remove(name);return e
 for name in eliminated:expand(name)
 deleted={definitions[x][0] for x in eliminated};remaining=[x for x in vs if x not in eliminated]
 residuals=[s.expand(row.subs(subs,simultaneous=True)) for i,row in enumerate(rows) if i not in deleted]
 req(all(not any(sym[x] in r.free_symbols for x in eliminated) for r in residuals),'all selected variables gone')
 ds=[s.Poly(r,*[sym[x] for x in remaining]).total_degree() for r in residuals];req(max(ds)*2==degree,'degree bound')
 Q=s.Poly(s.expand(sum(r*r for r in residuals)),*[sym[x] for x in remaining+fixed]);terms=Q.terms();mon=[0]*len(remaining+fixed);mon[remaining.index(witness[0])]=witness[1];mon[remaining.index(witness[2])]=witness[3]
 req(Q.coeff_monomial(tuple(mon))==1,'uniform leading monomial')
 out={'name':label+'_monic_projection','domain':'unrestricted integers','variables':remaining,'variable_count':len(remaining),'equation_count':len(residuals),'fixed_numerals':fixed,'coefficient_binding':p['coefficient_binding'],'residuals':[str(x) for x in residuals],'residual_degrees':ds,'single_polynomial':'sum of squares of residuals','exact_degree':degree,'degree_witness':{'monomial':witness[0]+'^'+str(witness[1])+'*'+witness[2]+'^'+str(witness[3]),'coefficient':1},'parent_sha256':hashlib.sha256((R/'quartic42.json').read_bytes()).hexdigest(),'eliminated_monic_coordinates':eliminated,'reconstruction':{str(k):str(v) for k,v in subs.items()},'proof':'PROJECTIONS.md'}
 (R/(label+'.json')).write_text(json.dumps(out,indent=2)+'\n')
 (R/(label+'_expanded.json')).write_text(json.dumps({'variables':remaining+fixed,'terms':[{'coefficient':int(c),'exponents':list(m)} for m,c in terms]},separators=(',',':'))+'\n')
 receipts.append({'name':label,'variables':len(remaining),'residuals':len(residuals),'max_residual_degree':max(ds),'degree':degree,'symbolic_terms':len(terms),'uniform_degree_witness':out['degree_witness']})
(R/'PROJECTION_CHECKS.json').write_text(json.dumps({'status':'PASS','variants':receipts,'scope':'Exact symbolic integer-monic projection and polynomial equality checks; inherited Q42 proof is separate.'},indent=2)+'\n');print(json.dumps(receipts,indent=2))

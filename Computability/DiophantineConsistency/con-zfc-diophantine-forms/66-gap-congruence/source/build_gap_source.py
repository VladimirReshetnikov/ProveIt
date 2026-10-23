#!/usr/bin/env python3
"""Independently reconstruct a gap-coordinate quadratic source and audit its code."""
import json,hashlib,itertools,math
from pathlib import Path
import sympy as s
R=Path(__file__).resolve().parent
HASH='1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287'
def demand(b,msg):
 if not b:raise ValueError(msg)
def main():
 raw=(R/'parent_source.json').read_bytes();demand(hashlib.sha256(raw).hexdigest()==HASH,'parent hash')
 src=json.loads(raw);names=src['variables'];ports=src['constants'];v=s.symbols(' '.join(names));pp=s.symbols(' '.join(ports));env=dict(zip(names+ports,v+pp))
 for k,x in src['affine_abbreviations'].items():env[k]=s.sympify(x.replace('^','**'),locals=env)
 old=[]
 for eq in src['equations']:
  a=s.expand(s.sympify(eq['residual'].replace('^','**'),locals=env))
  literal=sum(t['coefficient']*math.prod(x**n for x,n in zip(v+pp,t['powers'])) for t in eq['terms'])
  demand(s.expand(a-literal)==0,'source literal identity');old.append(a)
 sparse=old[:];sparse[13]=s.expand(old[13]+old[1]);sparse[14]=s.expand(old[14]+old[2])
 code=json.loads((R/'split_code.json').read_text());weights=code['weights'];target=dict(zip(code['order'],code['targets']));at=dict(zip(code['targets'],code['order']))
 reports=[]
 for variant,sub in [('gap87',{env['P']:env['P']+env['eta']+env['zeta']}),('gapN86',{env['P']:env['P']+env['eta']+env['zeta'],env['N']:env['N']+1}),('gapL86',{env['P']:env['P']+env['eta']+env['zeta'],env['L']:env['L']-1}),('gapNq85',{env['P']:env['P']+env['eta']+env['zeta'],env['N']:env['N']+env['q']})]:
  rows=[s.expand(x.subs(sub,simultaneous=True)) for x in sparse];equations=[];kernels=[{}, {}, {}];interactions=0;collisions=[]
  for j,row in enumerate(rows,1):
   terms=s.Poly(row,*v).terms()
   equations.append({'number':j,'residual':str(row),'terms':[{'powers':list(a),'coefficient':int(c)} for a,c in s.Poly(row,*(v+pp)).terms()]})
   for alpha,coef in terms:
    deg=sum(alpha);demand(deg<=2,'quadratic degree');exponent=target[j]-sum(a*w for a,w in zip(alpha,weights));demand(exponent>=0,'kernel exponent')
    fac=2 if deg<2 else math.prod(math.factorial(a) for a in alpha)
    demand(exponent not in kernels[deg],'kernel same-degree collision')
    kernels[deg][exponent]=s.expand(fac*coef)
    candidates=[()] if deg==0 else [(i,) for i in range(31)] if deg==1 else itertools.combinations_with_replacement(range(31),2)
    expected=tuple(i for i,a in enumerate(alpha) for _ in range(a))
    for mon in candidates:
     interactions+=1;e=exponent+sum(weights[i] for i in mon)
     if e in at and (at[e]!=j or mon!=expected):collisions.append([j,deg,exponent,list(mon),at[e]])
  degrees=[max(k) for k in kernels];records=sum(len(s.Poly(x,*v).terms()) for x in rows)
  out={'name':variant,'source_sha256':HASH,'variables':names,'constants':ports,'domain':'strictly positive integers','coordinate_map':{str(k):str(a) for k,a in sub.items()},'source_row_operations':code['source_row_operations'],'equations':equations}
  (R/(variant+'_source.json')).write_text(json.dumps(out,indent=2)+'\n')
  encoded={'variables':names,'ports':ports,'source_sha256':hashlib.sha256((R/(variant+'_source.json')).read_bytes()).hexdigest(),'code_sha256':hashlib.sha256((R/'split_code.json').read_bytes()).hexdigest(),'formula':'G(B,U)=D2(B)*U^2+D1(B)*U+D0(B)','kernels':[{'degree':deg,'terms':[{'exponent':ex,'coefficient':[{'port_powers':list(a),'integer':int(c)} for a,c in s.Poly(coef,*pp).terms()]} for ex,coef in sorted(k.items())]} for deg,k in enumerate(kernels)]}
  (R/(variant+'_kernels.json')).write_text(json.dumps(encoded,indent=2)+'\n')
  reports.append({'variant':variant,'records':records,'interactions':interactions,'degrees':degrees,'height':max(x+i*max(weights) for i,x in enumerate(degrees)),'collisions':collisions,'valid_existing_certificate':not collisions})
 demand(reports[0]['records']==87 and not reports[0]['collisions'],'gap87 certificate')
 (R/'GAP_SOURCE_CHECKS.json').write_text(json.dumps(reports,indent=2)+'\n');print(json.dumps(reports,indent=2))
if __name__=='__main__':main()

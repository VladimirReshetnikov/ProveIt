#!/usr/bin/env python3
"""Independent degree-upper-bound and leading-coefficient certificates."""
import json,random
import sympy as s
from check_complete_equations import ROOT,load,req,recval,evaluate

def leading(d,fix,p):
 ds=[];cs=[]
 for node in d['nodes']:
  k=node['kind']
  if k=='literal':dd,cc=0,int(node['value'])%p
  elif k=='fixed':dd,cc=0,fix[node['name']]
  elif k=='variable':dd,cc=1,1
  else:
   i,j=node['left'],node['right']
   if k=='mul':dd,cc=ds[i]+ds[j],cs[i]*cs[j]%p
   else:
    dd=max(ds[i],ds[j]);cc=((cs[i] if ds[i]==dd else 0)+(1 if k=='add' else -1)*(cs[j] if ds[j]==dd else 0))%p
  ds.append(dd);cs.append(cc)
 return ds[d['output']],cs[d['output']]

def main():
 # Exact identity replacing the high-degree cancellation in the nine equation.
 A,C,E,G,H=s.symbols('A C E G H');D=(A*A-1)*C*C+1;F=(A*A-1)*E*E+1;I=(G*G-1)*H*H+1
 MD,MF,MI=A*C,A*E,G*H
 delta=(C*C-1)*MF**2*MI**2+D*(E*E-1)*MI**2+D*F*(H*H-1)
 req(s.expand((MD*MF*MI)**2-D*F*I-delta)==0,'telescoping square identity')
 E0,O,V0,V1,a0,a1,dd=s.symbols('E0 O V0 V1 a0 a1 dd')
 direct=(E0-O*V0*V1)**2-O**2*(a0+V0**2*a1)
 cert=E0**2-2*E0*O*V0*V1+O**2*V0**2*(V1**2-a1)-O**2*a0
 req(s.expand(direct-cert)==0,'inner identity')
 report={'exact_polynomial_identities':2,'families':{}}
 rng=random.Random(10232026)
 for fam in ['nine','sun']:
  d=load('nine/generated/multitarget_nine_positive_degree_certificate.json' if fam=='nine' else 'sun/generated/multitarget_sun10.json')
  directd=load('nine/generated/multitarget_nine_positive.json') if fam=='nine' else d
  rows=[]
  for p in [101,1009,1000003]:
   if fam=='nine':fix={r['name']:recval(r['terms'],p) for r in d['coefficient_recipes']};fix['base_floor']=pow(2,d['base_floor_exponent'],p)
   else:
    data=load('sun/generated/quadratic_coefficients.json');fix={r['name']:recval(r['coefficient_polynomial_in_fixed_ports'],p) for r in data['records'] if r['name']};fix['beta_sun']=pow(2,d['beta_sun_exponent'],p)
   deg,lc=leading(d,fix,p);req(lc!=0,'nonzero leading coefficient')
   for k in range(40):
    x={v:rng.randrange(p) for v in d['variables']};req(evaluate(d,x,fix,p)[0]==evaluate(directd,x,fix,p)[0],'certificate/direct replay')
   rows.append({'prime':p,'degree_upper_bound':deg,'diagonal_coefficient_at_bound':lc})
  req(len({x['degree_upper_bound'] for x in rows})==1,'degree agreement')
  report['families'][fam]={'status':'pass','exact_degree':rows[0]['degree_upper_bound'],'attainment':rows,'direct_certificate_replays':120}
 print(json.dumps(report,indent=2))
if __name__=='__main__':main()

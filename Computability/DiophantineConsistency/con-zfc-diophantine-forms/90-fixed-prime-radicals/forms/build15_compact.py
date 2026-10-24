#!/usr/bin/env python3
from pathlib import Path
import json
from norm_dag import DAG
from build_forms import DEFS,PORTS,compile_expr

HERE=Path(__file__).resolve().parent

def build15():
 variables=['j','C','z','f','h','r','v','w','T','c','s','p1','p2','p3','xi']
 d=DAG(variables+PORTS);values={x:x for x in d.inputs};defs=[]
 for name,expr in DEFS:
  if name in ['m','Df']:continue
  if name=='J':expr='3*j+1'
  if name=='I':expr='(2*r+1)*c**2'
  if name=='V':expr='f*c*T-f**2*R-c'
  defs.append((name,expr))
 defs += [('guard','Nguard-1-p1**2-p2**2-p3*(p3+1)'),('strong','Q-Delta*(f**2-1)'),('Pfirst','2*u+k'),('carrier','2*D0+H*(xi+3*Pfirst+18*V)'),('rad_A','36*H**2*Afirst'),('rad_D','4*Cmain'),('Cnum','324*H**2*(Q*V**2-1)'),('U_norm','delta*(carrier**2-rad_A-rad_D)-Cnum'),('norm_inner','U_norm**2-4*delta**2*rad_A*rad_D-4*delta*(rad_A+rad_D)*Cnum'),('norm','norm_inner**2-64*delta**3*rad_A*rad_D*Cnum*carrier**2'),('answer','(1+4*strong)*(1+4*guard)*(1+4*norm)-1')]
 for name,expr in defs:values[name]=compile_expr(expr,d,values)
 return d.finish(values['answer'],{'name':'integer15_degree214','domain':'unrestricted integers','variables':variables,'variable_count':15,'fixed_ports':PORTS,'coefficient_binding':'coefficients/BINDING.json','exact_degree':214,'prefix_abbreviations':defs,'root_count':3,'denominator_exponent':4,'carrier_variant':'half_centered_first_and_auxiliary','norm_output':values['norm'],'degree_certificate':'COMPACT15_PROOF.md','norm_identity':'delta^4 times the ordinary three-root norm at carrier, with radicands rad_A,rad_D,Cnum/delta','finalizer':'(1+4*strong)*(1+4*guard)*(1+4*norm)-1=0'})

if __name__=='__main__':
 p=build15();(HERE/'integer15_degree214.json').write_text(json.dumps(p,indent=2)+'\n')
 m={k:p[k] for k in ['name','variable_count','exact_degree','live_binary_operations']};(HERE/'METRICS15.json').write_text(json.dumps(m,indent=2)+'\n');print(m)

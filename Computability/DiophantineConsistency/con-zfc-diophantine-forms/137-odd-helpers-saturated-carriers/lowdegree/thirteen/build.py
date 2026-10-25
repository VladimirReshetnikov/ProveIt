#!/usr/bin/env python3
"""Build the free-scale first-root/positivity norm in thirteen unrestricted integers."""
from pathlib import Path
import json, hashlib, gzip
from circuit import DAG, export
ROOT=Path(__file__).resolve().parent
VARS=['j','C','z','h','r','v','w','T','c','n','y','p1','p2']
PORTS=['beta','K0','MC','MF','cone_A','cone_B']
REGS=[
 ['J','6*j+1'], ['qm','beta*J'], ['q','qm+1'], ['W','12*w+4'],
 ['X','q*W'], ['Y','v'], ['F','(K0+W)*C-z*qm'],
 ['R','(q*(q-F)-C)*(q**2-1)+(MC+q*MF)*J'],
 ['E','X*Y'], ['a','E+Y'], ['H','4*a+3'], ['Delta','a**2+H'],
 ['k','R+1+h*E'], ['eta','c-Y*k'], ['L','E*(Y*k)'],
 ['I','(2*r+1)*c**2'], ['Ds','Delta*I**2'], ['Fs','1+Ds'], ['Q','Delta*Ds'], ['V','Fs*(c*T-R)-c'],
 ['q3','q*q**2'], ['M','2*q3'], ['U','M*H'], ['Klo','X*(2*X-3*c)-2'],
 ['Z','U*n+M*Klo+H*(Y-q3)'],
 ['Derr','(cone_A*F-q)**2+(cone_B*C-q)**2'],
 ['budget','(Y*k)**2*(q**2-Derr)-q**2*(4*(Y*eta)**2+(k*q3)**2)'],
 ['G','4*(budget-p1**2-p2**2)-3'],
 ['carrier','(Z+U*k)**2+4*U*(L*Z-U)'],
 ['auxiliary','V**2-(Q-1)*y*(2*V+y)-1'],
 ['Dt','1+L*(L+k)'], ['U2','U**2'],
 ['ga','U2*G'], ['db','4*U2*Dt'], ['fc','16*U2*Fs'], ['gc','ga+fc'],
 ['inner','(carrier-gc)**2-4*(ga*fc+db*gc)'],
 ['N','inner**2-64*ga*db*fc*(carrier+db)'],
 ['P','(N+1)*(auxiliary+1)-1']]

def build():
 d=DAG(VARS);env={x:d.leaf('variable',x) for x in VARS}
 env.update({x:d.leaf('coefficient',x) for x in PORTS})
 for name,form in REGS:env[name]=eval(form,{'__builtins__':{}},env)
 p=export('parity_separated_three_root_norm13_degree156',d,env['P'],{k:env[k] for k,_ in REGS},
    {'exact_degree':156,'fixed_numerals':PORTS,'proof':'PROOF.md',
     'proof_status':'Ordinary arithmetic reduction to the pinned normalized17 source. Not a new proof-assistant or internal object-ZFC certificate.'})
 p['coefficient_binding']='../coefficients/BINDING.json'
 return p

def main():
 p=build(); (ROOT/'equation.json').write_text(json.dumps(p,indent=2,sort_keys=True)+'\n')
 spec={'name':p['name'],'variables':VARS,'fixed_numerals':PORTS,'domain':'unrestricted integers',
       'polynomial_abbreviations':REGS,'single_polynomial':'P','exact_degree':156,
       'coefficient_binding':'../coefficients/BINDING.json','row_degrees':[22,36,18,120],
       'proof':'PROOF.md'}
 (ROOT/'specification.json').write_text(json.dumps(spec,indent=2,sort_keys=True)+'\n')
 print(json.dumps({k:p[k] for k in ['name','variable_count','exact_degree','operations','operation_counts']},sort_keys=True))
if __name__=='__main__':main()

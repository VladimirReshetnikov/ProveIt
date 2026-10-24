#!/usr/bin/env python3
"""Triple-centered three-root carrier over thirteen unrestricted integers."""
from pathlib import Path
import json,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent))
from circuit import DAG,export
VARS=['j','C','z','h','r','v','w','T','c','n','p1','p2','p3']
PORTS=['beta','K0','MC','MF','cone_A','cone_B']
REGS=[
 ['J','6*j+1'], ['qm','beta*J'], ['q','qm+1'], ['W','12*w+4'],
 ['X','q*W'], ['Y','q*v'], ['F','(K0+W)*C-z*qm'],
 ['R','(q*(q-F)-C)*(q**2-1)+(MC+q*MF)*J'],
 ['E','X*Y'], ['a','E+Y'], ['H','4*a+3'], ['Delta','a**2+H'],
 ['k','R+1+h*E'], ['eta','c-Y*k'], ['L','E*Y*k'],
 ['I','(2*r+1)*c**2'], ['Dfminus1','Delta*I**2'], ['Df','Dfminus1+1'],
 ['Q','Delta*Dfminus1'], ['V','Df*(c*T-R)-c'],
 ['M','2*q**2'], ['U','M*H'], ['Klo','2*X**2-3*X*c-2'],
 ['Z','U*n+M*Klo+H*(v-q**2)'],
 ['Derr','(cone_A*F-q)**2+(cone_B*C-q)**2'],
 ['budget','k**2*(q**2-Derr)-4*q**2*eta**2'],
 ['pos','1+p1**2+p2**2+p3*(p3+1)'],
 ['Aroot','2*L+k'], ['Broot','6*(a+2)*I'], ['Croot','9*(2*Q-1)*V'],
 ['Dtau','1+L*(L+k)'], ['Da','(Q-1)*(Q*V**2-1)'],
 ['Ztotal','Z+U*(Aroot+Broot+Croot)'], ['U2','U**2'],
 ['sroot','Ztotal**2'], ['uroot','4*U2*Dtau'], ['vroot','36*U2*Df'], ['wroot','324*U2*Da'],
 ['sw','sroot*wroot'], ['uv','uroot*vroot'],
 ['Ninner','(sroot+wroot-uroot-vroot)**2-4*(sw+uv)'],
 ['N','Ninner**2-64*sw*uv'],
 ['guard','budget-pos'], ['Sguard','guard**2'], ['P','N+Sguard+N*Sguard']]
def build():
 d=DAG(VARS);env={x:d.leaf('variable',x) for x in VARS}
 env.update({x:d.leaf('coefficient',x) for x in PORTS})
 for name,form in REGS:env[name]=eval(form,{'__builtins__':{}},env)
 p=export('triple_centered_carrier13_degree274',d,env['P'],{k:env[k] for k,_ in REGS},
 {'exact_degree':274,'fixed_numerals':PORTS,'proof':'PROOF.md','proof_status':'Ordinary reduction via fixed prime radical separation to adjacent fifteen-integer equation. Independent arithmetic and literal-circuit review passed; not a new end-to-end formal certificate.'})
 p['coefficient_binding']='../coefficients/BINDING.json'
 return p

def main():
 p=build();(ROOT/'equation.json').write_text(json.dumps(p,indent=2,sort_keys=True)+'\n')
 (ROOT/'specification.json').write_text(json.dumps({'name':p['name'],'variables':VARS,'fixed_numerals':PORTS,'domain':'unrestricted integers','polynomial_abbreviations':REGS,'single_polynomial':'P','exact_degree':274,'norm_degree':242,'guard_degree':16,'proof':'PROOF.md','coefficient_binding':'../coefficients/BINDING.json'},indent=2,sort_keys=True)+'\n')
 print(json.dumps({k:p[k] for k in ['name','variable_count','exact_degree','operations','operation_counts']},sort_keys=True))
if __name__=='__main__':main()

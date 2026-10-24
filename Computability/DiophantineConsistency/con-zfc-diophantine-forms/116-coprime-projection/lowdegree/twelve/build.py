#!/usr/bin/env python3
"""Direct four-root twelve-integer degree500 companion."""
from pathlib import Path
import json,sys
ROOT=Path(__file__).resolve().parent
BASE=ROOT.parent/'lowdegree' if (ROOT.parent/'lowdegree/circuit.py').is_file() else ROOT.parent
sys.path.insert(0,str(BASE))
from circuit import DAG,export
VARS=['j','C','z','h','r','v','w','T','c','n','p2','p3']
PORTS=['beta','K0','MC','MF','cone_A','cone_B']
BASE_REGS=json.loads((BASE/'thirteen/specification.json').read_text())['polynomial_abbreviations']
REGS=[]
for name,form in BASE_REGS:
 if name=='pos':form='1+p2**2+p3*(p3+1)'
 if name=='sw':break
 REGS.append([name,form])
REGS.extend([
 ['guard_radicand','budget-pos'], ['eroot','729*U2*guard_radicand'],
 ['p','uroot*vroot'], ['q4','wroot*eroot'], ['u','uroot+vroot'], ['v4','wroot+eroot'],
 ['s','sroot-u-v4'], ['k4','s**2-4*u*v4+4*(p+q4)'],
 ['l4','s+2*v4'], ['m4','s+2*u'],
 ['even','k4**2+16*(p*l4**2-q4*(m4**2+4*p))'],
 ['odd','k4*l4+8*q4*m4'], ['P','even**2-64*p*odd**2']])
def build():
 d=DAG(VARS);env={x:d.leaf('variable',x) for x in VARS}
 env.update({x:d.leaf('coefficient',x) for x in PORTS})
 for name,form in REGS:env[name]=eval(form,{'__builtins__':{}},env)
 p=export('four_root_carrier12_degree500',d,env['P'],{k:env[k] for k,_ in REGS},
 {'exact_degree':500,'fixed_numerals':PORTS,'proof':'PROOF.md','proof_status':'Ordinary four-root extension to the adjacent fifteen-integer equation. Independent arithmetic and literal-circuit review passed; not a new end-to-end formal certificate.'})
 p['coefficient_binding']='../coefficients/BINDING.json'
 return p
if __name__=='__main__':
 p=build();(ROOT/'equation.json').write_text(json.dumps(p,indent=2,sort_keys=True)+'\n')
 (ROOT/'specification.json').write_text(json.dumps({'name':p['name'],'variables':VARS,'fixed_numerals':PORTS,'domain':'unrestricted integers','polynomial_abbreviations':REGS,'single_polynomial':'P','exact_degree':500,'proof':'PROOF.md','coefficient_binding':'../coefficients/BINDING.json'},indent=2,sort_keys=True)+'\n')
 print(json.dumps({k:p[k] for k in ['name','variable_count','exact_degree','operations','operation_counts']},sort_keys=True))

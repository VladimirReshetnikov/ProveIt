#!/usr/bin/env python3
"""Adapt the credited compact four-root norm to the retained degree500 carrier."""
from pathlib import Path
import sys,json
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent))
from circuit import DAG,export
SPEC=json.loads((ROOT/'specification.json').read_text())
def build():
 d=DAG(SPEC['variables']); env={x:d.leaf('variable',x) for x in SPEC['variables']}
 env.update({x:d.leaf('coefficient',x) for x in SPEC['fixed_numerals']})
 for name,formula in SPEC['polynomial_abbreviations']: env[name]=eval(formula,{'__builtins__':{}},env)
 p=export(SPEC['name'],d,env['P'],{k:env[k] for k,_ in SPEC['polynomial_abbreviations']},{'exact_degree':500,'fixed_numerals':SPEC['fixed_numerals'],'proof':'PROOF.md','proof_status':'Pointwise-identical optimized evaluator of retained twelve-variable degree500 polynomial. Norm schedule credited to prior sources.'})
 return p
if __name__=='__main__':
 p=build(); (ROOT/'equation.json').write_text(json.dumps(p,indent=2,sort_keys=True)+'\n')
 print(json.dumps({k:p[k] for k in ['name','variable_count','exact_degree','operations','operation_counts']},sort_keys=True))

#!/usr/bin/env python3
"""Literal 15-integer norm with bounded-guard absorption; no finalizer."""
import json,sys,hashlib
from pathlib import Path
ROOT=Path(__file__).resolve().parent
SRC=ROOT/'source/con-zfc-parity-norms-2026-10-23'
sys.path.insert(0,str(SRC))
import build as base
from compact_norm import Circuit,eval_expr
p=json.loads((SRC/'parity15_unit_product.json').read_text())
old=p['polynomial_abbreviations']; new=[]
for name,formula in old:
    if name=='B_guard':
        new.extend([['r_main',p['factored_residuals'][0]],['r_strong',p['factored_residuals'][1]],
                    ['residual_budget','r_main**2+r_strong**2'],
                    ['budget_scale','q**2*k**2'],
                    ['b_absorbed','b_guard-budget_scale*residual_budget']])
        formula='4*b_absorbed+1'
    new.append([name,formula])
p.update(name='absorbed15_degree176',polynomial_abbreviations=new,factored_residuals=['norm15'],
         finalizer='none',single_polynomial='norm15',residual_count=1,exact_degree=176,
         source_parent='source/con-zfc-parity-norms-2026-10-23/parent/degree88_17.json',
         coefficient_binding='source/con-zfc-parity-norms-2026-10-23/coefficients/BINDING.json',
         proof_status='Ordinary bounded-guard absorption proof; inherited native/Pell/refutation calibration, not a new kernel certificate.')
ports=base.read_ports(); deg=base.evaluate(p,{v:base.Deg(1) for v in p['variables']},ports)[0].d
slopes=p['degree_certificate']['slopes']; uni=base.evaluate(p,{v:base.Uni([0,slopes[v]]) for v in p['variables']},{k:v%base.PRIME for k,v in ports.items()})[0]
if deg!=176 or len(uni.c)-1!=176:raise ValueError(('degree',deg,len(uni.c)-1))
p['degree_certificate']={'method':'safe degree bound and authentic-coefficient modular univariate specialization','prime':base.PRIME,'slopes':slopes,'final_degree':176,'final_leading_coefficient_mod_prime':uni.c[-1]}
c=Circuit();env={v:c.leaf(v) for v in p['variables']+p['fixed_numerals']}
for k,v in new:env[k]=eval_expr(v,env)
dag=c.export(env['norm15'],p['variables'],p['fixed_numerals'])
dag.update(name=p['name'],exact_degree=176,domain=p['domain'],coefficient_binding=p['coefficient_binding'])
(ROOT/'absorbed15_degree176.json').write_text(json.dumps(p,indent=2,sort_keys=True)+'\n')
(ROOT/'absorbed15_degree176_dag.json').write_text(json.dumps(dag,indent=2,sort_keys=True)+'\n')
receipt={'variables':len(p['variables']),'exact_degree':deg,'operations':dag['operations'],'counts':dag['counts'],'degree_certificate':p['degree_certificate'],'parent_packet_sha256':hashlib.sha256((SRC/'parity15_unit_product.json').read_bytes()).hexdigest()}
(ROOT/'ABSORPTION_METRICS.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
print(json.dumps(receipt,indent=2,sort_keys=True))

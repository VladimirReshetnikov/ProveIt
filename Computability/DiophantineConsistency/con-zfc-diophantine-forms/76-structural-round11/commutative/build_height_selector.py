#!/usr/bin/env python3
"""A four-way nonnegative selector lowers local degree50 to20."""
import json
from pathlib import Path
R=Path(__file__).resolve().parent
obj=json.loads((R/'height_shared_step.json').read_text())
obj['witnesses'].append('selector');obj['witness_count']=21
obj['selector_groups']=[[0,1,2,3],[9,4],[5,6,7],[8,10,11]]
obj['selector_nodes']=[0,1,2,3]
obj['polynomial']='(product_i(selector-i))^2 + sum_i(product_{j in selector_groups[i]} HornSOS[j])*(product_{k != i}(selector-k))^2 + E^2 + F^2'
obj['exact_degree']=20
(R/'height_selector_step.json').write_text(json.dumps(obj,indent=2)+'\n')
s=(R/'HeightCommutativeEquation.lean').read_text().replace('HeightCommutativeProposal','HeightSelectedCommutativeProposal').replace('Fin 5 ⊕ Fin 20','Fin 5 ⊕ Fin 21')
s=s.replace('UNCOMPILED and UNMATERIALIZED.','UNCOMPILED and UNMATERIALIZED. Four-way selector variant.')
old='  '+' * '.join('h'+str(i) for i in range(12))+' + e0 * e0 + e1 * e1'
new='  let r : Expr (Fin 5 ⊕ Fin 21) := .var (.inr 20)\n'
new+='  let g := r * (r - 1) * (r - 2) * (r - 3)\n'
for i in range(4):new+=f'  let l{i} := '+' * '.join('(r - '+str(j)+')' for j in range(4) if i!=j)+'\n'
new+='  g * g + '+' + '.join('('+' * '.join('h'+str(j) for j in group)+f') * l{i} * l{i}' for i,group in enumerate(obj['selector_groups']))+' + e0 * e0 + e1 * e1'
if old not in s:raise RuntimeError('Expected exact constructor output line missing')
s=s.replace(old,new)
(R/'HeightSelectedCommutativeEquation.lean').write_text(s)
print('Emitted21-local-witness degree20 selector and one-block uncompiled constructor')

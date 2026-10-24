#!/usr/bin/env python3
import json
from pathlib import Path
R=Path(__file__).resolve().parent
obj=json.loads((R/'height_shared_step.json').read_text())
obj['witnesses']+=['b0','b1','b2'];obj['witness_count']=23
obj['selector_groups']=[[9],[1,2],[3,4],[5,6],[7,8],[10,11],[0],[]]
obj['unused_group_value']=1
obj['polynomial']='sum_{k=0}^2 b_k^2*(b_k-1)^2 + sum_{i=0}^7 G_i*chi_i(b)^2 + E^2+F^2; G_i is product of listed HornSOS factors, empty product1; chi_i is multilinear Boolean indicator'
obj['exact_degree']=14
(R/'height_boolean_step.json').write_text(json.dumps(obj,indent=2)+'\n')
s=(R/'HeightCommutativeEquation.lean').read_text().replace('HeightCommutativeProposal','HeightBooleanCommutativeProposal').replace('Fin 5 ⊕ Fin 20','Fin 5 ⊕ Fin 23')
s=s.replace('UNCOMPILED and UNMATERIALIZED.','UNCOMPILED and UNMATERIALIZED. Three-bit selector variant.')
old='  '+' * '.join('h'+str(i) for i in range(12))+' + e0 * e0 + e1 * e1'
new=''
for k in range(3):new+=f'  let b{k} : Expr (Fin 5 ⊕ Fin 23) := .var (.inr {20+k})\n  let g{k} := b{k} * (b{k} - 1)\n'
for i in range(8):new+=f'  let l{i} := '+' * '.join(f'b{k}' if (i>>k)&1 else f'(1 - b{k})' for k in range(3))+'\n'
new+='  g0 * g0 + g1 * g1 + g2 * g2 + '+' + '.join('('+' * '.join('h'+str(j) for j in group)+f') * l{i} * l{i}' if group else f'l{i} * l{i}' for i,group in enumerate(obj['selector_groups']))+' + e0 * e0 + e1 * e1'
if old not in s:raise RuntimeError('Expected exact local output line missing')
s=s.replace(old,new)
(R/'HeightBooleanCommutativeEquation.lean').write_text(s)
print('Emitted23-local-witness degree14 one-block Boolean constructor')

#!/usr/bin/env python3
"""Count explicit serialized macro operators under a stated unit-macro convention."""
import collections,hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];path=D/'research/nine-seed33-jones-compact-macro-prototype/recipe.json';raw=path.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='06154f18e49d5ac3ca49add3a9b8bb03717f14590d2ef14f892d04b7dc3a75b3'
a=json.loads(raw);assert a['inputs']==9 and len(a['nodes'])==45 and a['output']=='output'
ring=collections.Counter();nat=collections.Counter()
def natural(t):
    if not isinstance(t,list) or not t:raise ValueError(t)
    op=t[0];nat[op]+=1
    if op in ('lit','index','expo') and len(t)==2:return
    if op in ('add','sub','mul','pow') and len(t)==3:
        natural(t[1]);natural(t[2]);return
    raise ValueError(t)
def term(t):
    if not isinstance(t,list) or not t:raise ValueError(t)
    op=t[0];ring[op]+=1
    if op in ('const','var','ref','fixed','pcoef') and len(t)==2:return
    if op in ('add','sub','mul') and len(t)==3:term(t[1]);term(t[2]);return
    if op=='pow' and len(t)==3:term(t[1]);natural(t[2]);return
    if op=='sum_range' and len(t)==4:natural(t[2]);term(t[3]);return
    if op=='sum_star' and len(t)==3:term(t[2]);return
    raise ValueError(t)
for node in a['nodes']:term(node['expr'])
ops=('add','sub','mul','pow','sum_range','sum_star')
out={'status':'PASS_EXTERNAL_SERIALIZED_MACRO_COUNT_ONLY','recipe_sha256':hashlib.sha256(raw).hexdigest(),'named_definitions':len(a['nodes']),'ring_operator_counts':{k:ring[k] for k in ops},'total_unit_macro_operators':sum(ring[k] for k in ops),'ring_leaf_occurrences':{k:ring[k] for k in ('const','var','ref','fixed','pcoef')},'natural_metadata_counts':dict(sorted(nat.items())),'convention':'Count one per explicit ring +,-,*,power,sum_range,sum_star node across the 45 named definitions, with each named ref shared, every explicit within-node occurrence counted, each sum body counted once, and exponent/bound syntax treated as free metadata. Leaves and fixed coefficient recipes are not arithmetic operations.','scope':'Count of this external serialized macro AST only; not a binary arithmetic circuit count, not a finite sum expansion or coefficient construction, and not a Lean-proved JSON semantic binding.'}
print(json.dumps(out,indent=2,sort_keys=True))

#!/usr/bin/env python3
"""Eliminate the q² witness syntactically; no Lean or large coefficients."""
import copy,hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1]
source=D/'research/nine-sharing-quartic65-sign33-candidate/seed.json';raw=source.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='a8cd4d01962b9380065ebbd3d7b75db3ffcadf18969099398bd151c4e2219e75'
a=json.loads(raw);assert a['jones_witness_count']==33 and len(a['residuals'])==24
first=a['residuals'][0];assert first['gate']=='q2' and first['kind']=='positive'
node=first['expr'];assert node[0]=='sub' and node[1]==['var',15]
replacement=node[2]
def transform(t):
    op=t[0]
    if op=='var':
        i=t[1]
        if i==15:return copy.deepcopy(replacement)
        return ['var',i-1 if i>15 else i]
    if op in ('num','port'):return copy.deepcopy(t)
    assert op in ('add','sub','mul') and len(t)==3
    return [op,transform(t[1]),transform(t[2])]
residuals=[]
for row in a['residuals'][1:]:
    out=copy.deepcopy(row);out['expr']=transform(row['expr']);residuals.append(out)
assert residuals[0]['gate']=='q3'
result={'schema':'sharing-sextic-substituted-q2-v1','source':'../nine-sharing-quartic65-sign33-candidate/seed.json','source_sha256':hashlib.sha256(raw).hexdigest(),'distinguished_input_coordinate':0,'witness_count':32,'total_coordinates':33,'coordinate_mapping':'old 0..14 unchanged; old 15 is q^2; old 16..33 map to new 15..32','substituted_q2':replacement,'fixed_ports':a['fixed_ports'],'coefficient_binding':a['coefficient_binding'],'residuals':residuals,'output':'sum of squares of the 23 displayed residuals','status':'source-only external candidate; no Lean proof, higher-degree Jones client, or endpoint'}
encoded=(json.dumps(result,indent=2,sort_keys=True)+'\n').encode();out=P/'seed.json'
if sys.argv[1:]==['--write']:
    with out.open('xb') as f:f.write(encoded)
elif sys.argv[1:]==['--check']:
    if out.read_bytes()!=encoded:raise RuntimeError('candidate differs')
    print(json.dumps({'status':'PASS_DETERMINISTIC_SUBSTITUTION_ONLY','seed_sha256':hashlib.sha256(encoded).hexdigest(),'scope':'Reproducible external AST substitution; no Lean or endpoint.'},sort_keys=True))
else:raise SystemExit('expected --write or --check')

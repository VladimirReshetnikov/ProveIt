#!/usr/bin/env python3
"""Check the finite lift/drop text and open target shapes without Lean."""
import hashlib,json,re,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
p=Path(__file__).resolve().parent;f=p/'SharingSeed25BridgeDraft.lean';s=f.read_text()
def vector(name):
 m=re.search(r'def '+name+r'\b[^\n]*\n  !\[([^\]]+)\]',s);assert m,name;return [x.strip() for x in m.group(1).split(',')]
lift=vector('lift');drop=vector('drop');assert lift==[*(f'v {i}' for i in range(19)),'v 17 * v 18',*(f'v {i}' for i in range(19,26))];assert drop==[*(f'v {i}' for i in range(19)),*(f'v {i}' for i in range(20,27))]
assert not re.search(r'(?m)^\s*(theorem|lemma)\s',s) and 'sorry' not in s and 'admit' not in s and 'def ForwardTarget' in s and 'def BackwardTarget' in s
assert 'InternalZero (SharingSeed25Octic.seed p) v →\n    InternalZero (SharingSeed26Sextic.seed p) (lift v)' in s
assert 'InternalZero (SharingSeed26Sextic.seed p) v →\n    InternalZero (SharingSeed25Octic.seed p) (drop v)' in s
for v in ([0]*26,list(range(26)),[i*i for i in range(26)]):
 up=v[:19]+[v[17]*v[18]]+v[19:];down=up[:19]+up[20:];assert down==v and up[0]==v[0] and up[19]>=0
print(json.dumps({'status':'PASS_SOURCE_MAPPING_ONLY','bridge_source_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'lift_length':len(lift),'drop_length':len(drop),'product_coordinate':19,'finite_controls':3,'scope':'Finite textual mapping and open target shapes only; no Lean compilation or zero-set theorem.'},indent=2,sort_keys=True))

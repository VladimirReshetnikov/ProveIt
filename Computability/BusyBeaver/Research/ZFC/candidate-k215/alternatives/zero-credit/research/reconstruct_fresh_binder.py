#!/usr/bin/env python3
"""Reconstruct the source-only fresh-binder experiment; no binary claim."""
from pathlib import Path
import json,hashlib,sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'code'))
import source_language as S

if not __debug__:raise RuntimeError('Assertions must be enabled')
raw=(ROOT/'reference/transfer201.sites.json').read_bytes()
parent=S.tree(json.loads(raw))
path='110100111010101100001011'
assert S.subtree(parent,path)==('CI',1)
source=S.replace(parent,path,(('CI',1),('CI',1)))
sites=S.sites(source)
assert sites==json.loads((ROOT/'research/transfer_gq.sites.json').read_text())
assert S.graph_arithmetic(sites)[0]==S.graph_intervals(sites)
metrics=S.metrics(source)
assert metrics=={'dag_nodes':201,'leaf_occurrences':4776,'maximum_depth':44,'maximum_zero_run':6}
cases=sum(2 if op=='CD'else 1 for _,op,_ in sites)
assert cases==6210
print(json.dumps({'status':'SOURCE_ONLY_FRESH_BINDER_RECONSTRUCTION_PASS','parent_sha256':hashlib.sha256(raw).hexdigest(),'source_sha256':hashlib.sha256((ROOT/'research/transfer_gq.sites.json').read_bytes()).hexdigest(),'metrics':metrics,'intended_guarded_cases':cases,'scope':'Exact source and two full CFG resolvers; no binary allocation or quantified-runtime certificate.'},indent=2))

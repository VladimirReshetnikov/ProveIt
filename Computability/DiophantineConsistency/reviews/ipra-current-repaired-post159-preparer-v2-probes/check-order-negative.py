#!/usr/bin/env python3
"""Exercise recorded-edge order checking without launching preparation."""
import ast,hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parent;P=D/'prepare.py';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();ph=H(P);sh=H(__file__)
tree=ast.parse(P.read_text());nodes=[x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name=='check_recorded_order'];assert len(nodes)==1
scope={};exec(compile(ast.Module(body=nodes,type_ignores=[]),str(P),'exec'),scope);check=scope['check_recorded_order'];assert check(['dependency','owner'],{'dependency':{'owner'}})==1
try:check(['owner','dependency'],{'dependency':{'owner'}})
except AssertionError as exc:failure=repr(exc);assert 'recorded dependency out of order' in failure
else:raise AssertionError('reversed recorded edge was accepted')
assert H(P)==ph and H(__file__)==sh
out={'status':'PASS_FAIL_CLOSED_RECORDED_ORDER','preparer_sha256':ph,'checker_sha256':sh,'positive_edge_count':1,'reversed_edge_failure':failure,'scope':'Pure isolated recorded-edge order probe; no replay or source graph validation.'};p=D/'order-negative-check.json';assert not p.exists();p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(out['status'],H(p))

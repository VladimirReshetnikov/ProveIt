#!/usr/bin/env python3
"""One explicit unproved1R45 interface used only to obtain a raw price."""
from pathlib import Path
import hashlib,json,sys,time
D=Path(__file__).resolve().parent;ROOT=D.parents[1]
sys.path.insert(0,str(ROOT/'research218_published_encoding'));import audit_construction as A
import provisional_allocator as P
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
oldpath=ROOT/'latest218_baseline/candidate-k218/sites218.json';tablepath=ROOT/'latest218_baseline/candidate-k218/k218.native.tm';newpath=D/'sites.json'
old=P.tree(json.loads(oldpath.read_text()));new=P.tree(json.loads(newpath.read_text()));beg=time.monotonic()
r=dict(status='UNPROVED_PROVISIONAL_GATE_RAW_PRICE',source_sha256=H(newpath),baseline_table_sha256=H(tablepath),gate={'op':'CD','counter':5,'side':1,'action':[1,1,45],'proved':False},source_nodes=len(P.nodes(new))+len({(o,a)for _,o,a in A.flatten(new)}),source_leaves=len(A.flatten(new)))
try:
 T,price=P.compile(A.R.table(tablepath),old,new);out=D/'provisional.raw.native.tm';out.write_bytes(P.M.enc(T));r.update(raw_price=price,raw_table_sha256=H(out))
except Exception as e:r.update(status='PROVISIONAL_ALLOCATOR_FAILURE_NOT_A_STATE_PRICE',error=repr(e))
if r.get('raw_price',{}).get('binding_failures'):r['status']='RAW_223_WITH_BINDING_DISCREPANCY_AND_UNPROVED_GATE'
r['seconds']=time.monotonic()-beg;r['scope']='The explicit rightCD5 action1R45 is an unproved primitive-interface obligation. The literal table may contain recorded role-binding discrepancies; it has no full runtime or blank proof. A raw price over218 is a stopping criterion for this exact proposal, not a lower bound on other layouts.'
(D/'PROVISIONAL_GATE_PRICE.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items()if k!='raw_price'},indent=2));print('price_summary',{k:v for k,v in r.get('raw_price',{}).items()if k!='changes'})

#!/usr/bin/env python3
"""One owned raw allocation pilot for the three exact proposed codec macros."""
from pathlib import Path
import hashlib,json,sys,time
D=Path(__file__).resolve().parent;ROOT=D.parent
sys.path.insert(0,str(ROOT/'research218_published_encoding'));import audit_construction as A
P=A.P
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def freeze(x):return tuple(map(freeze,x))if isinstance(x,list)else x
r=json.loads((D/'MACRO_INVENTORY.json').read_text());replacements={freeze(x['old_ast']):freeze(x['new_ast'])for x in r['inventory']}
base=ROOT/'latest218_baseline/candidate-k218/sites218.json';tm=ROOT/'latest218_baseline/candidate-k218/k218.native.tm';old=P.tree(json.loads(base.read_text()));counts={k:0 for k in replacements}
def replace(t):
 if t in replacements:counts[t]+=1;return replacements[t]
 if P.leaf(t):return t
 return(replace(t[0]),replace(t[1]))
new=replace(old);sites=A.flatten(new);sp=D/'three_macros.sites.json';sp.write_bytes(A.compact(sites));beg=time.monotonic()
result=dict(status='UNPROVED_RAW_COMPILER_PRICE',old_table_sha256=H(tm),old_source_sha256=H(base),new_source_sha256=H(sp),replacements=[dict(name=x['name'],occurrences=counts[freeze(x['old_ast'])])for x in r['inventory']],source_nodes=len(P.nodes(new))+len({(o,a)for p,o,a in sites}),primitive_occurrences=len(sites),new_primitives=sorted(set((o,str(a))for p,o,a in sites)-set((o,str(a))for p,o,a in A.flatten(old))))
try:
 T,price=P.compile(A.R.table(tm),old,new);tp=D/'three_macros.raw.native.tm';tp.write_bytes(P.M.enc(T));result.update(physical_price=price,raw_table_sha256=H(tp))
except Exception as e:result.update(status='ALLOCATOR_FAILURE_NOT_A_STATE_PRICE',error=repr(e))
result['seconds']=time.monotonic()-beg;result['scope']='One literal source replacement, not an enumeration. The source changes arithmetic codec and hence does not preserve the primitive CFG. Raw allocation and prefix checks do not certify runtime helper roles, changed-source scratch invariants, parser/stack semantics, fair enumeration or blank initialization.'
(D/'THREE_MACRO_PRICE.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

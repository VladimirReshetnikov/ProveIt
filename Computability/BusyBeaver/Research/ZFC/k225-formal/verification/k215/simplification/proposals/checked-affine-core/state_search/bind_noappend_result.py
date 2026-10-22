#!/usr/bin/env python3
"""Bind the universal CI receipt to exact source, table edit, and 214 table."""
from pathlib import Path
import hashlib,json

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def read(path):
    t={}
    for line in Path(path).read_text().splitlines():
        if line.strip() and not line.startswith('#'):
            q,b,w,d,z=line.split();t[int(q),int(b)]=(int(w),d,int(z))
    return t
def main():
    root=Path(__file__).resolve().parent;ref=root/'reference/k215';result=json.loads((root/'noappend_increment_universal.json').read_text())
    for p in [ref/'k215.native.tm',ref/'sites215.json',ref/'code/runtime-inputs/runtime/symbolic_runtime.py',ref/'code/runtime-inputs/runtime/independent_runtime.py',root/'symbolic_noappend_increment.py']:
        assert sha(p)==result['hashes'][p.name]
    mapping=json.loads((ref/'canonicalization.json').read_text());m={int(k):v for k,v in mapping['native_to_canonical'].items()};old=read(ref/'k215.native.tm');dense=read(root/'k215.tm')
    assert {(m[q],b):(w,d,m[z])for(q,b),(w,d,z)in old.items()}==dense
    assert [m[q]for q in [0,54,66,84,198,254]]==[0,54,66,83,189,215]
    assert old[66,0]==(1,'R',198) and dense[66,0]==(1,'R',189)
    new=dict(old);new[66,0]=(0,'L',54);new={k:v for k,v in new.items()if k[0]!=198}
    assert len(new)==428 and len({q for q,b in new})==214 and all(z!=198 for w,d,z in new.values())
    reachable={0};pending=[0]
    while pending:
        q=pending.pop()
        for b in (0,1):
            if (q,b) in new:
                z=new[q,b][2]
                if z not in reachable:reachable.add(z);pending.append(z)
    declared={q for q,b in new};unreachable=sorted(declared-reachable)
    assert len(declared & reachable)==212 and unreachable==[97,113]
    expected=('#! start 0\n'+''.join(f'{q} {b} {w} {d} {z}\n'for(q,b),(w,d,z)in sorted(new.items()))).encode()
    target=root/'rejected_noappend214.native.tm';assert target.read_bytes()==expected
    sites=json.loads((ref/'sites215.json').read_text());ids=[i for i,row in enumerate(sites)if row[1]=='CI'];assert len(ids)==1900
    assert result['status']=='ALL_CI_UNCHANGED_SPARE_CONTRACTS_PASS' and not result['failures']
    assert [c['site_index']for c in result['cases']]==ids
    assert all(len(c['duration'])==13 and c['duration'][0]>0 and all(x>=0 for x in c['duration'])for c in result['cases'])
    out={'status':'EXACT_TABLE_SOURCE_AND_1900_CASE_BINDING_PASS','native_edit':{'from':[66,0,1,'R',198],'to':[66,0,0,'L',54],'deleted':198},'dense_edit':{'from':[66,0,1,'R',189],'to':[66,0,0,'L',54],'deleted':189},'initial_state_native':0,'dispatcher_native':84,'dispatcher_dense':83,'halt_native':254,'working_states':214,'listed_working_states':214,'graph_reachable_working_states':212,'graph_unreachable_native_labels':unreachable,'rows':428,'source_leaf_occurrences':len(sites),'CI_cases':len(ids),'symbolic_rules':sum(c['symbolic_steps']for c in result['cases']),'minimum_duration_constant':min(c['duration'][0]for c in result['cases']),'skeleton_sha256':sha(target),'source_sha256':sha(ref/'sites215.json'),'universal_receipt_sha256':sha(root/'noappend_increment_universal.json'),'scope':'Exact binding for increment-only contracts. This table is a rejected full-machine experiment, with a zero-decrement first-clean-redispatch counterexample; its blank-run Con(ZFC) equivalence is not asserted or decided.'}
    (root/'noappend_binding.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()

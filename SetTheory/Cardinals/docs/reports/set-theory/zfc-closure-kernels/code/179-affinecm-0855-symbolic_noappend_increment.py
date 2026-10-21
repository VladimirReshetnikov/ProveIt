#!/usr/bin/env python3
"""Check all CI sites with exact unchanged spare suffix after one row edit.

Research sub-contract only: this altered table is not a consistency machine.
The inherited symbolic interpreter proves arbitrary unary values by scan/list
induction; this wrapper changes the CI postcondition from append-one to no
append and verifies every literal CI source occurrence.
"""
from pathlib import Path
import argparse,hashlib,importlib,json,sys,time

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--candidate-root',required=True);ap.add_argument('--out',default='noappend_increment_universal.json');a=ap.parse_args();root=Path(a.candidate_root)
    runtime=root/'code/runtime-inputs/runtime';sys.path.insert(0,str(runtime));s=importlib.import_module('symbolic_runtime')
    native=s.r.table(root/'k215.native.tm');assert native[66,0]==(1,1,198)
    native[66,0]=(0,-1,54);native={k:v for k,v in native.items()if k[0]!=198}
    assert all(z!=198 for w,d,z in native.values())
    m={int(k):int(v)for k,v in json.loads((root/'code/runtime-inputs/inputs/legacy_mapping.json').read_text()).items()}
    for q in {x for x,b in native}|{254}:
        if q not in m:m[q]=q+1000
    assert len({m[q]for q in {x for x,b in native}|{254}})==215
    T={(m[q],b):(w,d,m[z])for(q,b),(w,d,z)in native.items()};lemmas,blocks=s.prove_blocks(T)
    sites=json.loads((root/'sites215.json').read_text());selected=[(i,site)for i,site in enumerate(sites)if site[1]=='CI'];cases=[];bad=[];beg=time.time()
    for i,site in selected:
        try:
            ans=s.case(T,lemmas,site,False,append=None);cases.append({'site_index':i,'duration':ans['duration'],'motion':ans['motion'],'symbolic_steps':ans['symbolic_steps']})
        except Exception as e:bad.append({'site_index':i,'site':site,'reason':str(e)});break
        if len(cases)%500==0:print('proved',len(cases),'of',len(selected),'seconds',round(time.time()-beg,2),flush=True)
    result={'status':'ALL_CI_UNCHANGED_SPARE_CONTRACTS_PASS'if not bad and len(cases)==len(selected)else'NOT_PROVED','warning':'This is an increment-only research sub-contract. Zero-decrement contracts fail. No blank-start or Con(ZFC) claim for the edited table.','states_after_deletion':214,'changed_native_row':[66,0,0,'L',54],'deleted_native_label':198,'expected_CI_cases':len(selected),'proved_CI_cases':len(cases),'failures':bad,'blocks':blocks,'cases':cases,'seconds':time.time()-beg,'scope':'Every CI source occurrence, arbitrary nine natural logical register values, arbitrary natural gap, arbitrary nonempty finite natural spare suffix, whole tape with zero exterior. Output has exactly the same spare suffix. Mathematical induction checker, not proof-assistant kernel.','hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in [root/'k215.native.tm',root/'sites215.json',runtime/'symbolic_runtime.py',runtime/'independent_runtime.py',Path(__file__)]}}
    Path(a.out).write_text(json.dumps(result,indent=2)+'\n');print(result['status'],len(cases),'of',len(selected),round(time.time()-beg,2),flush=True)
if __name__=='__main__':main()

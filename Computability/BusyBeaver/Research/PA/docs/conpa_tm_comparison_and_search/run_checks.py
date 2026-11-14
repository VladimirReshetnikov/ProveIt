#!/usr/bin/env python3
"""Offline principal checks. Run with Python 3.11+; no third-party packages.

These are executable finite checks, not a Lean proof of nonhalting or a
lower bound. In particular rejected195 is expected to FAIL 93 contracts.
"""
from pathlib import Path
import sys, os, json, hashlib, subprocess, importlib.util, time
ROOT=Path(__file__).resolve().parent
os.chdir(ROOT)
sys.path.insert(0,str(ROOT/'support/work/optimize196'))
sys.path.insert(0,str(ROOT/'research_ipra/newsearch'))
import core
import rotation_search as rotation

def need(ok,msg):
    if not ok:raise AssertionError(msg)
def load_module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module

def literal_run(rows,start,limit,expected=None):
    q=start;head=0;ones=set()
    for steps in range(limit+1):
        if expected is not None and (q,head,ones)==expected:
            return {'clean_entry':True,'steps':steps,'state':q,'head':head,'one_cells':len(ones)}
        row=rows.get((q,int(head in ones)))
        if row is None:return {'halted':True,'steps':steps,'state':q,'head':head,'one_cells':len(ones)}
        if steps==limit:break
        w,right,q=row
        if w:ones.add(head)
        else:ones.discard(head)
        head+=1 if right else -1
    return {'halted':False,'clean_entry':False,'steps':limit,'state':q,'head':head,'one_cells':len(ones)}

def clean_entry():
    physical=[0,0,0,0,0,0,2,0,0]+[1]*26
    ones={-3,-2,46};pos=47
    for v in physical:
        pos+=1;ones.update(range(pos,pos+v+1));pos+=v+1
    return 84,-2,ones

def tree_from_sites(sites):
    trie={}
    for path,op,arg in sites:
        node=trie
        for b in path[:-1]:node=node.setdefault(b,{})
        node[path[-1]]=('leaf',op,arg)
    def convert(node):return tuple(convert(node[b]) for b in (0,1)) if isinstance(node,dict) else node
    return convert(trie)

def table_text(rows):
    return ''.join(f'{q} {b} {w} {"R" if d else "L"} {n}\n' for (q,b),(w,d,n) in sorted(rows.items()))

def main():
    started=time.monotonic();out={}
    checkdir=ROOT/'checks';checkdir.mkdir(exist_ok=True)
    cp=subprocess.run([sys.executable,'comparison/compare_all.py','--output','checks/comparison_replayed.json'],capture_output=True,text=True)
    need(cp.returncode==0,cp.stderr)
    c=json.loads((checkdir/'comparison_replayed.json').read_text())
    need(c['status']=='EXACT_COMPARISON_PASS','comparison')
    out['comparison']={'status':c['status'],'literal_tables':len(c['tables']),'u208_class_sizes':[5,4],'changed_common_rows':c['james_changed_common_rows']}
    print('Exact comparison: PASS (11 literal tables; two U208 classes)',flush=True)
    raw=(ROOT/'comparison/inputs/pa196.tm').read_bytes()
    need(hashlib.sha256(raw).hexdigest()=='e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8','PA196 bytes')
    rows,labels=core.machine();contracts=core.contracts()
    out['pa196_symbolic']=core.validate(rows,contracts)
    need(out['pa196_symbolic']['ok'] and out['pa196_symbolic']['contracts']==4959,'baseline symbolic')
    print('PA196 symbolic contracts: PASS (4959)',flush=True)
    out['pa196_startup']=literal_run(rows,74,58154,clean_entry())
    need(out['pa196_startup'].get('clean_entry') and out['pa196_startup']['steps']==58154,'startup')
    print('PA196 exact blank startup: PASS (58154 literal steps)',flush=True)
    obj=json.loads((ROOT/'research_ipra/newsearch/repairbase.json').read_text())
    candidate={(q,b):(w,d,n) for q,b,w,d,n in obj['rows']}
    candidate=rotation.merge(candidate,rotation.duplicates(candidate))
    need(len(candidate)==390,'rejected state count')
    tree=tree_from_sites(obj['sites'])
    need(rotation.cfg(tree)==core.program()[1],'rotation CFG')
    sites,cs=rotation.contract_list(tree);failed=[]
    for case in cs:
        if core.run(candidate,case) is None:failed.append({'site':case[0],'branch':case[1]})
    need(len(cs)==4959 and len(failed)==93,'rejected candidate failure count changed')
    out['rejected195']={'status':'REJECTED: source simulation fails','working_states':195,'same_resolved_source_cfg':True,'contracts':len(cs),'failed_contracts':len(failed),'first_failure':failed[0]}
    reject=ROOT/'rejected195';reject.mkdir(exist_ok=True)
    (reject/'rejected195.native.tm').write_text(table_text(candidate))
    states=[74]+sorted({q for q,b in candidate}-{74});mapping={q:i for i,q in enumerate(states)};mapping[254]=195
    dense={(mapping[q],b):(w,d,mapping[n]) for(q,b),(w,d,n) in candidate.items()}
    (reject/'rejected195.tm').write_text(table_text(dense))
    (reject/'STATUS.json').write_text(json.dumps(out['rejected195'],indent=2)+'\n')
    (reject/'failed_contracts.json').write_text(json.dumps(failed,indent=2)+'\n')
    print('Rejected 195-state quotient: reproduced 93 failures (expected)',flush=True)
    shortened={k:v for k,v in rows.items() if k[0] not in (15,23,34)}
    shortened[9,0]=rows[34,0]
    out['rejected_scanner_blank']=literal_run(shortened,74,1000)
    need(out['rejected_scanner_blank'].get('halted') and out['rejected_scanner_blank']['steps']==699,'scanner counterexample')
    print('Rejected scanner shortening: halts from blank at step 699 (expected)',flush=True)
    barrier=load_module('barrier',ROOT/'proof_notes/check_reflexivity_barrier.py')
    out['reflexivity_regression']=barrier.run()
    need(out['reflexivity_regression']['all_checks_passed'],'barrier regression')
    print('Reflexivity-barrier numerical regression: PASS',flush=True)
    alternate={}
    for line in (ROOT/'research196/accepted196_register_swap/pa196_register_AD_swap.tm').read_text().splitlines():
        q,b,w,d,n=line.split();alternate[labels[int(q)],int(b)]=(int(w),d=='R',labels[int(n)])
    saved_physical=core.PHYSICAL[:]
    core.PHYSICAL[:]=[6,2,0,3,4,7,8,5,1]
    alternate_check=core.validate(alternate,core.contracts())
    core.PHYSICAL[:]=saved_physical
    alternate_start=literal_run(alternate,74,58122,clean_entry())
    need(alternate_check['ok'] and alternate_check['contracts']==4959,'register-swapped contracts')
    need(alternate_start.get('clean_entry') and alternate_start['steps']==58122,'register-swapped startup')
    out['new196_register_swap']={'working_states':196,'runtime':alternate_check,'startup':alternate_start,'scope':'Executable checks; no new Lean proof and no state reduction'}
    print('New196-state A/D register swap: PASS (4959 contracts;58122 startup steps)',flush=True)
    out['overall_status']='REPRODUCIBLE_COMPARISON_AND_NEGATIVE_SEARCH; NO_SUB196_CONSTRUCTION'
    out['new_lean_biconditional_proved']=False
    out['seconds']=round(time.monotonic()-started,3)
    (checkdir/'verification_result.json').write_text(json.dumps(out,indent=2)+'\n')
    print('All expected checks completed. This is not a successful sub-196 construction.',flush=True)
if __name__=='__main__':main()

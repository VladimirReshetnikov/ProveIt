#!/usr/bin/env python3
"""Read completed direct-leaf evidence; no proof or supplied program execution."""
import hashlib,json
from pathlib import Path
BASE=Path('/tmp/zfc-intake188-opening');E=BASE/'execution';R=BASE/'review'
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def d(p):return {'path':str(p),'sha256':h(p),'size':p.stat().st_size}
def j(p):return json.loads(p.read_text())
def main():
    actual=j(E/'result.json');assert actual['status']=='FRESH_DIRECT_LEAVES_PASS'
    assert len(actual['jobs'])==6 and all(x['returncode']==0 and not x['timed_out'] and x['inputs_unchanged'] for x in actual['jobs'])
    for x in actual['jobs']:
        for k in ('stdout','stderr'):assert h(Path(x[k]))==x[k+'_sha256']
        assert not Path(x['stderr']).read_bytes()
    plan=j(E/'plan.json');assert h(E/'plan.json')==actual['plan_sha256']
    for x in plan['inputs']:assert h(Path(x['path']))==x['sha256']
    o=E/'output';c=j(o/'construction/construction.json');s=j(o/'independent_source_and_alias.json');b=j(o/'independent_blank_startup.json');r=j(o/'runtime/runtime.json');a=j(o/'runtime_audit.json')
    assert c['status']=='EXACT_K218_CONSTRUCTION_PASS' and s['status']=='PASS'
    assert (c['working_states'],c['transition_rows'],c['graph_reachable_states'])==(218,436,218)
    assert b['status']=='PASS' and b['verified_steps']==312909 and b['final_one_count']==277 and b['exact_complete_tape_equality']
    assert r['status']=='ALL_PRIMITIVE_INTERFACES_PROVED' and (r['cases'],r['symbolic_steps'],r['minimum_actual_steps'])==(6167,1515158,12)
    assert len(r['directly_used_native_rows'])==436 and a['status']=='INDEPENDENT_K218_RUNTIME_INTEGRITY_AND_COVERAGE_PASS'
    supplied=j(E/'packet/portable/reference_results/runtime.json')
    assert {k:v for k,v in r.items() if k!='seconds'}=={k:v for k,v in supplied.items() if k!='seconds'}
    pp=j(BASE/'portable-prepared/plan.json')
    def norm(v,root):return json.loads(json.dumps(v).replace(str(root),'{WORK}'))
    assert norm(plan,E)==norm(pp,BASE/'portable-prepared')
    receipt={'status':'FRESH_DIRECT_LEAVES_EVIDENCE_REVIEW_PASS','reviewer':'opening_encoder','role':'Read full executable closure; authored and ran direct-leaf adapter and this evidence reader; not an independent reviewer of own adapter. Submitted proof/leaf authorship unchanged.','findings':[],
      'actual':d(E/'result.json'),'plan':d(E/'plan.json'),'source_review':d(R/'source-review.md'),
      'selected_inputs':plan['inputs'],'review_code':[d(R/n) for n in ('prepare.py','run.py','prepare_portable.py','run_portable.py','prepare-portable.diff','run-portable.diff','finalize_review.py')],
      'portable_preparation':d(BASE/'portable-prepared/plan.json'),'portable_plan_path_normalized_equal':True,'portable_runtime_rerun':False,
      'counts':{'jobs':6,'states':218,'rows':436,'source_dag_nodes':205,'leaves':4744,'runtime_cases':6167,'symbolic_steps':1515158,'startup_steps':312909,'startup_one_cells':277,'minimum_duration_constant':12},
      'raw_runtime_matches_delivered_except_seconds':True,'no_stderr':True,'all_selected_inputs_unchanged':True,'scope':plan['scope'],'exclusions':plan['exclusions'],
      'output_records':[d(p) for p in sorted(o.rglob('*')) if p.is_file()]}
    (R/'review.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n');print(h(R/'review.json'))
if __name__=='__main__':main()

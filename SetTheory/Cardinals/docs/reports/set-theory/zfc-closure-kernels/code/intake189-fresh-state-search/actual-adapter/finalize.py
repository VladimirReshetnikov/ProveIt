#!/usr/bin/env python3
"""Own inert terminal-evidence review, no supplied program invocation."""
import hashlib,json,sys
from pathlib import Path
B=Path('/tmp/zfc-intake189-opening');E=B/'execution';R=B/'review'
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def d(p):return {'path':str(p),'sha256':h(p),'bytes':p.stat().st_size}
def j(p):return json.loads(p.read_text())
def main():
    a=j(E/'result.json');assert a['status']=='FRESH_DIRECT_LEAVES_PASS' and len(a['jobs'])==5
    for row in a['jobs']:
        assert row['returncode']==0 and not row['timed_out'] and row['inputs_unchanged']
        for field in ('stdout','stderr'):assert h(Path(row[field]))==row[field+'_sha256']
        assert not Path(row['stderr']).read_bytes()
    p=j(E/'plan.json');assert a['plan_sha256']==h(E/'plan.json')
    for row in p['inputs']:assert h(Path(row['path']))==row['sha256']
    assert j(E/'output/rho6-closure.json')['status']=='EXACT_CLOSED_RHO6_SUBTREE_REPLACEMENT_PASS'
    reports={}
    for v,n,steps in [('rho6_219',6167,1516088),('nop219',6175,1508163)]:
        q=E/'output'/v;r=j(q/'runtime.json');s=j(q/'startup.json');binding=j(q/'binding.json');c=j(q/'runtime-comparison.json')
        assert r['status']=='ALL_PRIMITIVE_INTERFACES_PROVED' and (r['cases'],r['symbolic_steps'])==(n,steps)
        assert s['status']=='DUAL_COMPLETE_BLANK_STARTUP_PASS' and s['steps']==312617 and len(s['complete_one_cells'])==277
        assert (binding['states'],binding['rows'])==(219,438)
        assert c['status']=='FRESH_EXACT_ORDERED_CASE_REPLAY_PASS' and c['exact_delivered_case_bytes']
        before=j(E/'packet/verification/recorded'/v/'runtime.json')
        assert {k:x for k,x in r.items() if k!='seconds'}=={k:x for k,x in before.items() if k!='seconds'}
        reports[v]={'cases':n,'symbolic_steps':steps,'startup_steps':312617,'complete_one_cells':277,'states':219,'rows':438,'runtime_receipt':d(q/'runtime.json'),'case_array':d(q/'runtime_cases.json'),'source_receipt':d(q/'source.json'),'binding_receipt':d(q/'binding.json'),'startup_receipt':d(q/'startup.json')}
    result={'status':'SELECTED_STATERESEARCH_LEAVES_REVIEW_PASS','reviewer':'opening_encoder','role':'Author of direct adapters; full selected supplied closure read; own inert evidence review; no independent-review claim for own adapter.','findings':[],'actual':d(E/'result.json'),'plan':d(E/'plan.json'),'variants':reports,'total_cases':12342,'runtime_record_matches_except_seconds':True,'all_selected_inputs_unchanged':True,'all_stderr_empty':True,'python':sys.version,'scope':p['scope'],'exclusions':p['exclusions'],'portable_preparation':d(R/'portable-review.json'),'review_sources':[d(x)for x in sorted(R.iterdir()) if x.is_file() and x.name!='review.json']}
    (R/'review.json').write_text(json.dumps(result,indent=2)+'\n');print(h(R/'review.json'))
if __name__=='__main__':main()

#!/usr/bin/env python3
"""Own inert reader of completed fresh190 evidence. Never imports delivered code."""
from pathlib import Path
import argparse,hashlib,json

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return json.loads(p.read_text())
def desc(p): return {'path':str(p),'sha256':sha(p),'size':p.stat().st_size}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--work',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();w=a.work.resolve();out=a.out.resolve();assert not out.exists()
 r=read(w/'result.json');plan=read(w/'plan.json');p=w/'packet';o=w/'output'
 assert r['status']=='FRESH_DIRECT_LEAVES_PASS' and r['plan_sha256']==sha(w/'plan.json')
 assert len(r['jobs'])==6 and r['inputs_unchanged']
 assert [x['name'] for x in r['jobs']]==[x['name'] for x in plan['jobs']]
 for j in r['jobs']:
  assert j['returncode']==0 and j['timed_out'] is False and j['inputs_unchanged']
  assert sha(Path(j['stdout']))==j['stdout_sha256'] and sha(Path(j['stderr']))==j['stderr_sha256']
  assert Path(j['stderr']).read_bytes()==b''
 assert all(sha(Path(x['path']))==x['sha256'] and Path(x['path']).stat().st_size==x['size'] for x in plan['inputs'])
 assert len(r['exact_delivered_output_matches'])==11
 for x in r['exact_delivered_output_matches']:
  assert x['equal'] and Path(x['actual']).read_bytes()==Path(x['delivered']).read_bytes() and sha(Path(x['actual']))==x['sha256']
 src=read(o/'source/verification.json');lin=read(o/'construction/lineage.json');can=read(o/'canonical/canonicalization.json')
 rt=read(o/'runtime/runtime.json');cases=read(o/'runtime/cases.json');audit=read(o/'runtime/integrity.json');start=read(o/'runtime/startup.json')
 assert src['status']=='ALL_NATURAL_SOURCE_BISIMULATION_PASS' and len(src['stages'])==3
 assert src['stages'][-1]['metrics']=={'dag_nodes':205,'leaf_occurrences':4744,'maximum_depth':38,'maximum_zero_run':6}
 assert all(s['primitive_count']==4744 and s['guarded_successors']==6166 and s['no_stray_suffix_checks']==6167 and s['first37_PC_equal'] for s in src['stages'])
 assert lin['status']=='PINNED_UPSTREAM219_TO_K218_EXACT_LINEAGE_AND_SOURCE_BISIMULATION_PASS' and len(lin['stages'])==7
 assert all(s['complete_guarded_CFG_equal'] and s['primitive_word_equal'] and s['first37_addresses_equal'] and s['prefix_binding']['prefixes']==4743 and s['prefix_binding']['unknown_exterior_reads']==0 for s in lin['stages'])
 assert (lin['stages'][-1]['states'],lin['stages'][-1]['transition_rows'])==(218,436)
 assert rt['status']=='ALL_GENERIC_PRIMITIVE_INTERFACES_PROVED' and rt['failures']==[] and rt['generic_cases_excluded']==0
 assert rt['cases']==rt['expected_cases']==len(cases)==6167
 sites=read(o/'construction/candidate.sites.json')
 assert [(x['index'],x['positive']) for x in cases]==[(i,b) for i,(_,op,arg) in enumerate(sites) for b in ((False,True) if op=='CD' else (False,))]
 assert sum(x['symbolic_steps'] for x in cases)==rt['symbolic_steps']==1514325
 assert min(x['duration'][0] for x in cases)==13
 assert len(rt['directly_used_rows'])==len({tuple(x) for x in rt['directly_used_rows']})==436
 assert audit['status']=='INDEPENDENT_EXACT_TABLE_UNBOUNDED_STARTUP_AUDIT_PASS'
 assert (audit['working_states'],audit['transition_rows'],audit['generic_cases'],audit['symbolic_steps'],audit['minimum_duration_constant'],audit['directly_used_rows'])==(218,436,6167,1514325,13,436)
 assert len(audit['independently_rederived_block_schemas'])==4
 assert all(sha(o/'runtime'/n)==h for n,h in audit['hashes'].items())
 assert start==read(o/'startup-only/startup.json')
 s=start['startup'];assert (s['steps'],s['state'],s['head'],len(s['ones']),s['all_other_cells'])==(312701,84,-5,277,0)
 assert s['logical_registers']==[3,0,0,0,3,0,0,0,0] and s['spares']==[1]*130
 assert s['sparse_and_dense_agree'] and s['header']==139 and s['extra_gap']==80
 delivered=read(p/'certificates/runtime/runtime.json');diffkeys=sorted(k for k in set(rt)|set(delivered) if rt.get(k)!=delivered.get(k));assert diffkeys==['seconds']
 assert start==read(p/'certificates/runtime/startup.json')
 receipt={'status':'EXISTING_FRESH_SOURCE147_EVIDENCE_REVIEW_PASS','reviewer':'opening_encoder','reviewer_role':'Author of direct preparation/runner and this inert metadata reader; read full delivered leaf/import closure, then ran selected delivered leaves on a disposable copy. Independent ordinary proof/source review is supplied separately by the other reviewers. No proof-assistant claim.',
 'actual':desc(w/'result.json'),'plan':desc(w/'plan.json'),'inputs_current':len(plan['inputs']),'jobs':6,'all_returncodes_zero':True,'empty_stderr':True,'exact_delivered_outputs':11,'runtime_only_report_difference':diffkeys,
 'counts':{'states':218,'rows':436,'source_dag':205,'source_leaves':4744,'source_guards':6167,'source_successors':6166,'lineage_stages':7,'decoder_prefixes_each_stage':4743,'runtime_cases':6167,'symbolic_steps':1514325,'minimum_duration_constant':13,'directly_used_rows':436,'startup_steps':312701,'startup_ones':277},
 'records':[desc(o/q) for q in ['source/verification.json','source/ordinal_correspondence.json','construction/lineage.json','canonical/canonicalization.json','startup-only/startup.json','runtime/startup.json','runtime/runtime.json','runtime/cases.json','runtime/integrity.json']],
 'scope':plan['scope'],'exclusions':plan['exclusions'],'history':'Reviewer preparation attempt1 failed before any supplied execution because of inherited188 path assumptions; exact helper/diff/receipt retained. No delivered job failed.','findings':[]}
 out.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n');print(out,sha(out))
if __name__=='__main__': main()

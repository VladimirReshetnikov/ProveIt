#!/usr/bin/env python3
"""Own metadata/semantic-result audit only; no supplied imports, invocation or simulation."""
import argparse,csv,hashlib,json
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('--execution',type=Path,required=True);ap.add_argument('--review',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
E=a.execution.resolve();W=a.review.resolve();O=E/'outputs';P=E/'packet'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text())
checks=[]
def need(value,label):
 if not value:raise AssertionError(label)
 checks.append(label)
plan=load(W/'replay-plan.json');actual=load(E/'actual.json');pins=load(W/'reviewed-inputs.json')
need(actual['status']=='SIX_SELECTED_PROCESSES_EXIT_ZERO_PENDING_RESULT_AUDIT','terminal root aggregate awaiting semantic audit')
need(actual['selected_names']==[j['name'] for j in plan['jobs']],'exact selected six names')
need(len(actual['jobs'])==6,'six terminal jobs')
def expand(s):return s.replace('{COPY}',str(P)).replace('{OUT}',str(O)).replace('{BASE219}',str(E/'baseline219'))
for got,want in zip(actual['jobs'],plan['jobs']):
 need(got['name']==want['name'] and got['exit_code']==0 and got['timeout'] is False,'terminal '+want['name'])
 need(got['argv'][1:]==[expand(x) for x in want['argv'][1:]],'exact command '+want['name'])
 need(got['cwd']==str(P) and got['timeout_seconds']==120,'cwd and cap '+want['name'])
 need((E/'logs'/(want['name']+'.stderr')).read_bytes()==b'','empty stderr '+want['name'])
for j in plan['jobs']:
 for name in j['reviewed_closure']:
  pin=next(x for x in pins['fully_read_code'] if x['path']==name)
  need(sha(P/name)==pin['sha256'],'executed reviewed bytes '+name)
for x in plan['baseline_inputs']:need(sha(E/'baseline219'/x['relative_target'])==x['sha256'],'selected baseline '+x['relative_target'])
pe=load(O/'peirce.json')
for k,n,p,r,ks in [('four_value',256,16,['F','T','A','C'],[]),('five_value',500,25,['F','T','B','C'],[[1,3],[2,1],[3,2]])]:
 d=pe[k];need(d['status']=='FINITE_PREMISES_PASS' and d['restricted_rho8_checks']==n and d['peirce_checks']==p and d['restrictions']==r and d['K_failures']==ks,'precise Peirce scope '+k)
need(pe==load(P/'theory/peirce_hc_countermodels.json'),'whole finite-model receipt equals delivered comparison')
b=load(O/'residual-blocks.json');need(b['status']=='PASS' and b['blocks']['status']=='SYMBOLIC_BLOCK_COMPOSITIONS_PASS','residual statuses')
need([b['source'][x] for x in ['comparator_cases','repaired_gate_cases','nip_cases','dirty_reader_cases','dirty_reload_cases']]==[289,729,17,1089,289],'five residual finite censuses')
need(b['blocks']['axiom_rows']==[{'commands':38,'row':i}for i in range(1,9)],'all eight axiom blocks')
need([b['blocks'][x]for x in ['bundle_commands','generalization_cases','modus_ponens_cases','discard_cases','reset_cases']]==[36,3,9,12,12],'compiler block counts')
need(b['blocks']['arbitrary_state_start'] and b['blocks']['final_falsum_test'] and b['blocks']['induction_premise'].startswith('BUILD(X)'),'induction premise retained explicitly')
need(b==load(P/'theory/counter_salt_blocks.json'),'whole residual receipt equals delivered comparison')
enc=load(O/'encoding/encoding_reproduction.json');src=load(O/'encoding/source_reconstruction.json');ar=load(O/'encoding/arithmetic.json');au=load(O/'encoding/counter_salt_source_audit.json')
need(enc['status']=='PASS_ENCODING_REPRODUCTION' and src['status']=='PASS_SOURCE_RECONSTRUCTION','source reconstruction statuses')
need(enc['reconstructed_source_sha256']==src['output_sha256']==sha(O/'encoding/counter_salt_208.sites.json')=='dc32510df9ffb07c2e106d835f735baff4a19989198a7f5bfec3f34e0046559d','exact repaired source bytes')
need(len(src['equality_replacement_paths'])==4 and src['selected_association']==[0,1],'four replacements and selected association')
need(len(src['repaired_associations'])==4 and all(x['dag_nodes']==208 and x['leaf_occurrences']==4741 and x['maximum_zero_run']==6 for x in src['repaired_associations']),'four repaired source costs')
need(ar['status']=='PASS_FINITE_ARITHMETIC' and ar['cases_per_macro']==4165 and [x['status'] for x in ar['macros']]==['PASS','PASS'],'both4165-input arithmetic probes')
need(au['status']=='PASS_LITERAL_SOURCE_MACRO_CROSS_AUDIT' and au['source_leaf_count']==4741 and au['source_sha256']==src['output_sha256'],'actual-source cross-audit binding')
need(au['acceleration_checks']['finite_cases']=={'transfer':340,'pair':343,'unpair':650,'asymmetric':289},'1622 separate acceleration probes')
need(len(au['discard_reset_cases'])==6 and au['initial_AX0_cases']==18 and au['source_node_visits']==54578,'actual-source symbolic contract census')
need(all(x['discard']=='PASS' and x['reset']==('HALTS' if x['T_case']==['n',[1]] else 'PASS')for x in au['discard_reset_cases']),'early halting distinguished from reset endpoint')
for name in ['encoding_reproduction.json','source_reconstruction.json','arithmetic.json','counter_salt_source_audit.json']:need(load(O/'encoding'/name)==load(P/'encoding/receipts'/name),'whole encoding receipt comparison '+name)
t=load(O/'two-adic/summary.json');need(t['status']=='PASS_SOURCE_COST_AND_FINITE_HELPERS' and t['helper_diagnostic_cases']==644,'two-adic status/count')
need([(x['metrics']['dag_nodes'],x['metrics']['leaf_occurrences'])for x in t['variants']]==[(206,4744),(214,5614),(217,5088),(225,5958)],'all codec costs')
need(t['diagnostics']['dirty_destination_witness']=={'a':1,'b':0,'initial_r7':1,'actual_r7':3,'required_for_additive_offset_pairer':2},'dirty destination witness retained')
for x in t['variants']:need(sha(O/'two-adic'/x['source'])==x['sha256'],'emitted codec source '+x['source'])
need(t==load(P/'experiments/two_adic/receipts/summary.json'),'whole two-adic receipt comparison')
lit=load(E/'logs/literal-deltas.stdout');need([x['working_states']for x in lit]==[218,219,223],'three literal state counts')
for x in lit:
 f=P/'machine'/x['name'];need(sha(f/'machine.native.tm')==x['table_sha256'] and sha(f/'sites.json')==x['source_sha256'],'literal table/source '+x['name'])
need(all('four-occurrence' in x['source_recipe']for x in lit[:2]),'two exact four-occurrence source recipes')
traces=[]
for name,reg,steps,status in [('gate_counterexample',1,[16342,12398],'EXACT_VALID_INTERFACE_FRESHNESS_GATE_COUNTEREXAMPLE'),('cache_forge_counterexample',5,[14420,11056],'EXACT_VALID_INTERFACE_CACHED_ONE_FORGERY')]:
 d=load(O/'weak-counterexamples'/(name+'.json'));need(d['status']==status,'counterexample status '+name)
 need([r['steps'] for r in d['runs']]==steps,'counterexample step counts '+name)
 need([r['dispatches'][-1]['logical_registers'][reg]for r in d['runs']]==[0,1],'observed corruption '+name)
 need(all(r['all_other_cells']==0 and r['initial_state']==84 and r['initial_head']==0 and r['initial_spares']==[0]for r in d['runs']),'complete-frame conventions '+name)
 for r in d['runs']:
  path=O/'weak-counterexamples'/r['trace_csv'];need(sha(path)==r['trace_sha256'],'recorded trace hash '+r['trace_csv'])
  rows=list(csv.DictReader(path.open()));need(len(rows)==r['steps'] and all(int(x['tick'])==i for i,x in enumerate(rows)),'recorded trace cardinality/order '+r['trace_csv'])
  traces.append({'file':str(path.relative_to(E)),'rows':len(rows),'sha256':sha(path)})
 need(d==load(P/'machine/weak218_rejected'/(name+'.json')),'whole fresh counterexample equals delivered comparison '+name)
result={'status':'INDEPENDENT_SIX_JOB_SEMANTIC_RECORD_AUDIT_PASS','reviewer':'drop_contract','scope':'Independent source-reviewed semantic-result/command/input/log/trace-metadata reading. No supplied rerun, machine simulation, algebra re-execution, proof compiler or full runtime. Root performed the six actual jobs.','checks':len(checks),'check_labels':checks,'root_actual_sha256':sha(E/'actual.json'),'root_runner_sha256':sha(E/'run.py'),'plan_sha256':sha(W/'replay-plan.json'),'source_review_sha256':sha(W/'review.json'),'jobs':6,'seconds_sum':sum(x['seconds']for x in actual['jobs']),'raw_traces':traces,'results':{'peirce_checks':[16,25],'restricted_rho8_checks':[256,500],'residual_gate_cases':729,'arithmetic_cases_per_macro':4165,'actual_source_leaf_count':4741,'actual_source_dag':208,'codec_helper_cases':644,'codec_matched_dag':225,'literal_states':[218,219,223],'weak_corruption_steps':[[16342,12398],[14420,11056]]},'nonclaims':['No new<=216 machine','No optional job ran','No full primitive runtime ran','Finite model premises are distinct from the ordinary unbounded HC proof','Weak caller witnesses are not claimed blank-reachable'],'evidence_files':[{'path':str(p.relative_to(E)),'bytes':p.stat().st_size,'sha256':sha(p)}for folder in ['logs','outputs']for p in sorted((E/folder).rglob('*'))if p.is_file()]}
a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':result['status'],'checks':len(checks),'sha256':sha(a.output)},indent=2))

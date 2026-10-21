#!/usr/bin/env python3
"""Independently audit saved selected Source164 outcomes; executes no candidate."""
import argparse,hashlib,json
from pathlib import Path

def ident(p):
 b=p.read_bytes();return {'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def load(p):return json.loads(p.read_text())
def table(p):
 out={}
 for line in p.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();k=(int(q),int(b));v=(int(w),d,int(z))
  assert k not in out and k[1] in (0,1) and v[0] in (0,1) and d in ('L','R');out[k]=v
 return out

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--run',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 run=a.run.resolve();r=load(run/'actual.json');p=Path(r['disposable_packet']);o=run/'outputs'
 assert r['status']=='PASS_PROCESS_AND_INPUT_BINDINGS' and r['wall_cap_seconds_per_job']==60
 assert r['inputs_unchanged'] and r['before']==r['after']==r['original']==r['original_after']
 for n,b in r['before'].items():assert ident(p/n)==b
 names=['construction','projection','projection-independent','context-matrix','matrix-lifting','residual-contracts','scanner-counterexample']
 assert [j['name'] for j in r['jobs']]==names
 for j in r['jobs']:
  assert j['exit_code']==0 and not j['timed_out'] and 0<=j['elapsed_seconds']<60
  assert j['argv'][1]=='-B'
  for stream in ('stdout','stderr'):assert ident(run/j[stream]['path'])=={k:v for k,v in j[stream].items() if k!='path'}
  assert (run/j['stderr']['path']).stat().st_size==0
 for n,b in r['outputs'].items():assert ident(o/n)==b
 c=load(o/'construction/construction.json');assert c['status']=='PASS_DETERMINISTIC_K215_COMPOSITION' and len(c['machines'])==1
 m=c['machines'][0];assert (m['permutation'],m['working_states'],m['rows'],m['guarded_cases'])==('210',215,430,6176)
 assert m['source_metrics']=={'dag_nodes':202,'leaf_occurrences':4751,'maximum_depth':47,'maximum_zero_run':6}
 assert m['full_guarded_CFG_equal_to_calibrated_public_permutation'] and m['both_inherited_marker_fold_rows_preserved']
 assert (m['new_decoder_nodes'],m['retained_subtree_roles'],m['retained_decoder_states'],m['deleted_states'],m['changed_retained_rows'])==(22,157,143,[185],36)
 for n,target in [('k215.native.tm','candidate215/k215.native.tm'),('k215.tm','candidate215/k215.tm'),('sites215.json','candidate215/sites215.json')]:assert (o/'construction'/n).read_bytes()==(p/target).read_bytes()
 t=table(o/'construction/k215.native.tm');d=table(o/'construction/k215.tm');mapping={int(k):v for k,v in load(o/'construction/canonicalization.json')['native_to_canonical'].items()}
 assert len(t)==len(d)==430 and len(mapping)==len(set(mapping.values()))==216 and mapping[0]==0 and mapping[254]==215
 assert {(mapping[q],b):(w,dr,mapping[z]) for (q,b),(w,dr,z) in t.items()}==d
 sites=load(o/'construction/sites215.json');assert len(sites)==4751 and sum(2 if x[1]=='CD' else 1 for x in sites)==6176
 pr=load(o/'projection.json');pi=load(o/'projection-independent.json')
 assert pr['verified'] and pr['leaf_counts']=={'zero':224,'epsilon':164,'L':1,'R':754,'LL':50,'RR':62,'LLR':1,'RRR':2,'LLRR':2}
 assert pr['source_certificate_sha256']==pi['sha256']==ident(p/'theory/dominated_rho8_full_certificate.json')['sha256']
 assert pi['proof_nodes']==pr['forward_proof']['proof_nodes']==3728 and pi['source_terms']==pr['forward_proof']['shared_terms']==5160
 assert pi['rules']==pr['forward_proof']['rules']=={'dominated_rho8':1260,'mp_substitution':55,'truth':1,'substitution':410,'mp':2002}
 assert pi['all_roots_verified']==['I','K','P','cd59','B','S','rho8']
 assert pi['minimum_literal_certificate_cover']==9 and len(pi['optimal_covers'])==6
 normalize=lambda xs:sorted('zero' if x=='ZERO' else x for x in xs)
 assert sorted(normalize(x) for x in pi['optimal_covers'])==sorted(normalize(x['functions']) for x in pr['literal_cover_minimum']['all_six_optimal_covers'])
 cm=load(o/'context-matrix.json');lm=load(o/'matrix-lifting.json')
 assert cm['table']==lm['matrix']==[[3,3,2,3],[3,3,3,3],[0,3,3,3],[0,1,2,3]]
 assert cm['context_family_assignments']=={'epsilon':64,'L':256,'R':256,'RRR':4096} and cm['zero_family_assignments']==64
 assert cm['zero_alias'] and cm['modus_ponens'] and cm['rho8_counterexample_value']==cm['B_value']==cm['S_value']==2
 assert (lm['implication_homomorphism_cases'],lm['raw_family_cases'],lm['proper_prefix_low_seed_escape_cases'],lm['constant_truth_family_cases'])==(9216,524288,5129,64)
 assert lm['unrestricted_raw_witness']=={'A':2,'B':1,'C':3,'U':1,'code':2526379112,'value':2}
 rc=load(o/'residual-contracts.json');assert rc['status']=='PASS' and rc['total_tests']==sum(rc['tests'].values())==4619
 assert rc['tests']=={'reset':243,'setter':432,'opposite_residual_setter':432,'row_selection':864,'bundle_selection':81,'generalization_inductive_step':648,'modus_ponens_inductive_step':1728,'terminal_refutation_detection':36,'wire_roundtrip_and_cursor_decrease':155}
 sc=load(o/'scanner-counterexample.json');assert sc['status']=='REACHABLE_SOURCE_FRAME_REFINEMENT_COUNTEREXAMPLE'
 assert sc['source_steps_from_initial_dispatch']==1474 and sc['site_index']==40 and sc['site'][1:]==['CD',1]
 sf=sc['source_frame'];assert sf['registers']==[7,0,0,0,4,0,0,0,0] and (len(sf['spares']),sf['gap_extra'],sf['absolute_head'])==(546,495,-9)
 old,new=sc['runs']['accepted'],sc['runs']['shortened'];assert old['matches_expected'] and not new['matches_expected']
 assert (old['steps'],new['steps'])==(4546,4622) and old['decoded_frame']['next_source_ordinal']==43 and new['decoded_frame']['next_source_ordinal']==66
 assert old['support_symmetric_difference_from_expected']==[] and new['support_symmetric_difference_from_expected']==[13,15]
 assert old['support']==sc['expected_one_cells'] and sorted(set(new['support'])^set(old['support']))==[13,15]
 result={'status':'PASS_INDEPENDENT_SAVED_SEMANTIC_AUDIT','actual':ident(run/'actual.json'),'auditor':ident(Path(__file__)),
 'selected_jobs':7,'selected_inputs':len(r['before']),'process_logs_and_input_bindings':True,
 'reconstruction':{'states':215,'rows':430,'source_leaves':4751,'guarded_cases':6176,'DAG':202,'canonical_bijection':True},
 'projection':{'nodes':3728,'terms':5160,'leaves':1260,'roots':7,'minimum_fixed_certificate_cover':9,'optimal_covers':6},
 'matrix':{'finite_homomorphism':9216,'raw_family_cases':524288,'prefix_escapes':5129,'full_native_model':False},
 'residual_interface_cases':4619,'scanner':{'reached_source_steps':1474,'old_successor':43,'mutated_successor':66,'blank_failure_claim':False},
 'scope':'Own saved-output audit; no candidate, source checker, runtime or blank replay. Ordinary universal proofs were read separately. Source162 runtime transfer is separate.'}
 a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()

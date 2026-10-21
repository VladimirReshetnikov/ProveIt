#!/usr/bin/env python3
"""Read-only independent audit of five saved Source154 theory runs; no child execution."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path

NAMES=[('mp-conventions','check_mp_conventions.py','mp_conventions_receipt.json'),('membership-blind','check_membership_blind_detachment.py','membership_blind_receipt.json'),('shifted-even','check_shifted_even_codec.py','shifted_even_codec_receipt.json'),('negative-atoms','check_negative_atoms_core_matrix.py','negative_atoms_core_matrix_receipt.json'),('t-template','check_t_template.py','t_template_receipt.json')]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def desc(p):return {'path':str(p),'sha256':sha(p)}
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--records',required=True,type=Path);ap.add_argument('--packet',required=True,type=Path);ap.add_argument('--output',required=True,type=Path);a=ap.parse_args()
 records=a.records.resolve();packet=a.packet.resolve();r=json.loads((records/'actual.json').read_text())
 assert r['status']=='FIVE_SELECTED_THEORY_LEAVES_PASS' and r['inputs_unchanged'] is True
 assert r['wall_limit_seconds_each']==60 and r['assertions_enabled'] is True
 assert r['selected_source_before']==r['selected_source_after']
 assert len(r['jobs'])==5 and [j['name']for j in r['jobs']]==[x[0]for x in NAMES]
 def read_bound(d):
  old=Path(d['path']);p=records/old.relative_to(Path(r['output']))
  assert p.is_file() and sha(p)==d['sha256'] and p.stat().st_size==d['bytes']
  return p
 receipts=[];identities=[]
 for job,(name,script,out) in zip(r['jobs'],NAMES):
  assert job['exit_code']==0 and job['timed_out'] is False and 0<=job['elapsed_seconds']<60
  assert job['argv'][1]=='-B' and Path(job['argv'][2]).name==script and len(job['argv'])==3
  current=packet/'research/theory'/script
  assert sha(current)==r['selected_source_before'][script]['sha256']==job['source']['sha256']
  assert job['source']['bytes']==current.stat().st_size
  stdout=read_bound(job['stdout']);stderr=read_bound(job['stderr']);assert stderr.read_bytes()==b''
  p=read_bound(job['fresh_output']);assert p.name==out
  x=json.loads(p.read_text());printed=json.loads(stdout.read_text())
  assert printed==({k:v for k,v in x.items()if k!='cases'} if name=='t-template' else x)
  receipts.append(x);identities.append({'name':name,'source':desc(current),'output':desc(p)})
 m,i,s,n,t=receipts
 assert m['status']=='SYMBOLIC_BLOCK_CONTRACTS_PASS'
 assert m['conventions']==['no_push_copy','no_push_move','no_push_cache'] and m['opaque_stack_tails'] is True
 assert m['checks']=={'discard':27,'axiom_leaves':216,'bundle':27,'gen':135,'mp':675,'whole_program':675}
 assert m['total']==sum(m['checks'].values())==1755 and 'induction-hypothesis placeholder' in m['scope']
 assert i['status']=='MEMBERSHIP_BLIND_RULE_REGRESSION_PASS'
 assert i['exact_I_Q_E_field_checks']==129*129*3 and i['arithmetic_case_checks']==100001
 assert i['two_element_irreflexive_models']==4 and i['semantic_rule_checks']==4*10001
 assert i['satisfied_rule_premises']==3764 and i['safe_halt_code_checks']==17500
 assert i['negative_control']=={'cached':6,'wrong_fields':[0,1],'premises_valid':True,'conclusion_valid':False}
 # Literal negative control: Q(1,0)=6 is true, wrong unpair(2)=(0,1) turns truth into falsum.
 pair=lambda x,y:(x+y)*(x+y+1)//2+y
 assert 4*pair(1,0)+2==6 and pair(0,1)==2 and 4*pair(0,0)+1==1
 assert 'not a K/ZFC model' in i['scope']
 assert s['status']=='SHIFTED_EVEN_CODEC_ARITHMETIC_REGRESSIONS_PASS' and s['field_checks']==129*129*2 and s['natural_code_cases']==100001
 assert s['exact_on']==['I*','Q*'] and s['unconstrained_on']==['R','J']
 ip=lambda x,y:max(0,4*pair(x,y)-2)
 assert ip(0,0)==4*pair(0,0)==0 and ip(ip(0,1),1)==s['minimum_double_negation_code']==114
 assert 'Not a native-calculus formalization' in s['scope']
 assert n['claim']=='CORE_MATRIX_ONLY; no native K or equiconsistency claim'
 assert n['implication']==[[3,3,3,3],[3,3,0,3],[3,3,3,3],[0,0,1,3]] and (n['F'],n['designated'])==(0,3)
 assert n['checked']['distribution_value_pair_sets']==2**16-1 and n['checked']['rho6_value_sets']==2**4-1 and n['checked']['restricted_L_F_instances']==4**3
 assert all(n['checked'][k] is True for k in ('modus_ponens','identity','explosion','GEN'))
 C=n['implication'];I=lambda x,y:C[x][y];N=lambda x:I(x,0)
 aa,bb,cc,uu=n['full_L_failure_abcu'];assert I(I(I(cc,uu),aa),I(I(aa,cc),I(bb,cc)))==n['full_L_failure_value']==0
 assert sorted({N(x)for x in range(4)})==n['negative_values']==[0,3]
 assert all(N(N(x))==(3 if x==3 else 0)for x in range(4)) and n['double_negation_normalizes_to_boolean'] is True
 assert n['I_Q_closure_of_negative_values']==[0,1,2,3]
 assert t['status']=='EXACT_BOOLEAN_TEMPLATE_PASS' and t['dual_rho6_BDD_equalities']==8 and len(t['cases'])==12
 expected=[(same,list(flags))for same in (False,True)for flags in itertools.product((False,True),repeat=2 if same else 3)]
 assert [(c['coincident_input_output_labels'],c['time_advancing_quantifiers'])for c in t['cases']]==expected
 for c in t['cases']:
  assert c['symbolic_boolean_variables']==32 and c['all_valuations_represented']==2**32
  assert c['checked_BDD_equalities']==(36 if c['coincident_input_output_labels'] else 64)
 assert t['total_BDD_equalities']==sum(c['checked_BDD_equalities']for c in t['cases'])==656
 assert 'not a finite model of the full theory' in t['scope']
 out={'status':'SAVED_FIVE_THEORY_LEAVES_REVIEW_PASS','findings':[],'actual':desc(records/'actual.json'),'reviewer_source':desc(Path(__file__).resolve()),'bindings':identities,'fresh_child_seconds':sum(j['elapsed_seconds']for j in r['jobs']),'all_five_exit_zero':True,'all_stderr_empty':True,'no_timeouts':True,'input_scripts_unchanged':True,'semantic_counts':{'symbolic_block_regressions':1755,'inverse_decoder_fields':49923,'inverse_arithmetic_inputs':100001,'two_element_semantic_checks':40004,'shifted_fields':33282,'shifted_inputs':100001,'distribution_value_pair_sets':65535,'rho6_value_sets':15,'template_BDD_equalities':656,'dual_B_BDD_equalities':8},'scope':'Read-only saved-record/raw-log/source-binding and semantic-field audit. Literal negative-control/matrix witness arithmetic checked independently. No child execution, no complete BDD proof reimplementation, no model-existence or machine certification claim.'}
 with a.output.open('x')as f:f.write(json.dumps(out,indent=2)+'\n')
 print(json.dumps({'status':out['status'],'fresh_child_seconds':out['fresh_child_seconds'],'actual_sha256':out['actual']['sha256']},indent=2))
if __name__=='__main__':main()

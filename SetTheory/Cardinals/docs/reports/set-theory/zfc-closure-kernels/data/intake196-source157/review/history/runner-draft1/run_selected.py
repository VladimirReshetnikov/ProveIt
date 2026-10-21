#!/usr/bin/env python3
"""Bounded six-leaf replay on a new disposable copy; no delivered wrappers."""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys,time,traceback

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def dump(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
def gates(name,x):
 g=[]
 def ck(ok,label):
  if not ok:raise AssertionError((name,label))
  g.append(label)
 if name=='scanner-local':
  ck(x['status']=='EXACT_LOCAL_WHOLE_TAPE_PROOF','local proof status')
  ck(x['removed_state']==50 and x['patches']==[[34,0,1,-1,196],[77,1,0,-1,75]],'exact deletion and patches')
  ck([(a['old_steps'],a['new_steps'])for a in x['cases']]==[(1,1),(2,4),(3,3)],'all three positive blocks')
  ck(all(a['endpoint'][2]==a['constrained_cells']for a in x['cases']),'all constrained cells restored')
  ck(len(x['assumptions'])==2,'retained contextual premises')
 elif name=='literal-packet':
  ck(x['status']=='PACKET_LITERAL_EVIDENCE_PASS'and x['verified_217_state_consistency_machine']is False,'literal evidence only')
  ck([(r['working_states'],r['transitions'])for r in x['tables']]==[(218,436),(218,436),(217,434),(217,434),(220,440)],'all five table censuses')
  ck(x['exact_patches_checked']is True,'literal patch comparisons')
  a=x['short_scanner_startup'];b=x['short_scanner_counterexample']
  ck((a['steps'],a['state'],a['head'],a['pc'],a['gap'],a['header'])==(104082,84,-6,'',6,64),'complete root startup endpoint')
  ck(a['logical_registers']==[4,3,0,0,3,0,0,0,0]and a['spares']==[1]*59 and len(a['one_cells'])==139,'whole seed and spare list')
  ck((b['ordinal'],b['expected_steps'],b['actual_steps'])==(40,588,662),'literal counterexample clocks')
  ck(b['expected']['pc']=='110100100100001'and b['actual']['pc']=='1101001001001','wrong returned source address')
  ck(b['expected_one_cells']!=b['actual_one_cells'],'whole-tape distinction')
 elif name=='restricted-L-matrices':
  ck(x['status']=='PASS'and len(x['matrices'])==2,'two complete finite matrices')
  a,b=x['matrices']
  for row in [a,b]:
   ck(row['status']=='PASS'and row['logical_rows_checked']==['rho1','rho2','rho3','rho4','rho5','rho6','G']and row['checks_per_row']==27,'seven rows / 27 assignments '+row['name'])
   ck(row['designated']==[0]and row['native_alias_I00']==0 and row['inference_rules_checked']==['truth','modus_ponens','closed_GEN'],'native alias and rules '+row['name'])
  ck(a['matrix']['restrictions']==['A']and b['matrix']['restrictions']==['B','C','0','1'],'exact restricted families')
  ck(a['counterexample_values']==[2,2,1]and a['counterexample_value']==2 and b['counterexample_values']==[1,0]and b['counterexample_value']==1,'S and K failures')
  ck(a['additional_valid_rows']==['identity','K','explosion','double_negation_elimination','quantifier_stability']and b['additional_valid_rows']==['identity','double_negation_elimination','quantifier_stability'],'extra row scopes')
  ck([r['excluded_gated_bundle_counterexample']for r in[a,b]]==[dict(native_parameters=[1,3,0],value=1),dict(native_parameters=[1,3,0],value=2)],'full bundle explicitly excluded')
 elif name=='seed-reflexivity':
  ck(x['status']=='PASS'and x['closed_proof_nodes']==79 and x['native_conclusion']==3,'closed 79-node conclusion3')
  ck(x['rules']=={'G':1,'K':19,'S':15,'gen':1,'mp':40,'rho1':1,'rho2':1,'rho6':1},'exact rule census')
  ck('derived' in x['inherited_basis']and'not a new' in x['scope'],'inherited basis and proof-assistant boundary')
 elif name=='local7-source-counterexample':
  ck(x['status']=='PASS_SOURCE_COUNTEREXAMPLE'and x['old_source_prefix']=='11101','exact source-level witness')
  ck(x['after_replacement']==dict(T=5,W=44861733172689145030,D=1,H=0,X=0,Y=0),'exact replacement tuple')
  ck(x['after_wrong_MP']==dict(T=1,W=1006287551628778831536508661218666293160,D=1,H=0),'exact wrong-MP tuple')
  ck(x['suffix']==['DROP','NIP','NIP']and x['suffix_halts']is True,'literal halting suffix')
  ck('No independent binary' in x['scope'],'no physical blank-run claim')
 elif name=='source-recodings':
  ck(x['status']=='EXACT_SOURCE_RECODING_CERTIFICATES_PASS'and len(x['records'])==6,'six complete source certificates')
  ck(x['baseline_metrics']==dict(dag_nodes=203,leaf_occurrences=4751,maximum_depth=45,maximum_zero_run=6),'exact baseline source census')
  ck(x['graph_sha256']=='932f126d86a86f7822a0d1b00e0940711d6c91702db75373667ffbd8e4247a20'and x['primitive_word_sha256']=='62e6b76f945ae63027da2592a8bacd29e2a5e23ec6210271a728017e31ae3ba8','full graph and word bindings')
  for i,r in enumerate(x['records']):
   m=r['metrics'];ck(m['leaf_occurrences']==4751 and m['dag_nodes']==(205 if i==0 else206)and m['maximum_zero_run']==(6 if i==0 else5),'source metrics '+r['file'])
   ck(all(r[k]is True for k in ['primitive_word_equal','guarded_CFG_equal','two_CFG_resolvers_agree','initializer37_equal']),'full equalities '+r['file'])
 else:raise ValueError(name)
 return g

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--plan',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 assert __debug__ and not sys.flags.optimize
 plan=json.loads(a.plan.read_text());out=a.output.resolve();out.mkdir(parents=True,exist_ok=False)
 (out/'logs').mkdir();(out/'output').mkdir();(out/'history').mkdir()
 src=Path(plan['package']);copy=out/'work';shutil.copytree(src,copy)
 # Preserve all code/input predecessors before the only approved adapter edit.
 for rel in ['source-layout/verify_sources.py','source-layout/receipts/verification.json','verification/packet.json']:
  q=out/'history'/rel;q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(copy/rel,q)
 pins=plan['inspected_closure']+plan['selected_data'];before={r['path']:sha(copy/r['path'])for r in pins}
 assert all(before[r['path']]==r['sha256']for r in pins)
 for job in plan['jobs']:
  for e in job.get('edits',[]):
   p=copy/e['file'];s=p.read_text();assert s.count(e['before'])==1;p.write_text(s.replace(e['before'],e['after']))
 assert sha(copy/'source-layout/verify_sources.py')==plan['adapter']['successor']['sha256']
 frozen={r['path']:sha(copy/r['path'])for r in pins}
 rec=dict(status='RUNNING',runner_sha256=sha(__file__),plan_sha256=sha(a.plan),original_package=str(src),copy=str(copy),python_executable=sys.executable,python_version=sys.version,optimization=sys.flags.optimize,original_inputs=before,adapted_inputs=frozen,jobs=[])
 dump(out/'actual.json',rec)
 try:
  for j in plan['jobs']:
   sub=lambda s:s.replace('{COPY}',str(copy)).replace('{OUT}',str(out/'output'))
   cmd=[sub(s)for s in j['argv']];env=os.environ.copy();env.update(j['env']);t=time.monotonic()
   log=out/'logs'/(j['name']+'.stdout');err=out/'logs'/(j['name']+'.stderr')
   item=dict(name=j['name'],argv=cmd,cwd=sub(j['cwd']),environment_overrides=j['env'],timeout_seconds=j['timeout'],stdout=str(log),stderr=str(err),status='RUNNING')
   rec['jobs'].append(item);dump(out/'actual.json',rec)
   with log.open('wb')as so,err.open('wb')as se:
    proc=subprocess.run(cmd,cwd=item['cwd'],env=env,stdout=so,stderr=se,timeout=j['timeout'])
   item.update(exit_code=proc.returncode,seconds=time.monotonic()-t,stdout_sha256=sha(log),stderr_sha256=sha(err))
   assert proc.returncode==0,('nonzero process',j['name'])
   if j['output_files']:
    f=Path(sub(j['output_files'][0]));data=json.loads(f.read_text())
   else:data=json.loads(log.read_text())
   item['semantic_gates']=gates(j['name'],data)
   dest=out/'output'/(j['name']+'.json');dump(dest,data)
   item.update(status='PASS',result=str(dest),result_sha256=sha(dest));dump(out/'actual.json',rec)
   print(j['name'],'PASS',round(item['seconds'],3),len(item['semantic_gates']),flush=True)
  after={r['path']:sha(copy/r['path'])for r in pins}
  assert after==frozen,'source/data drift during replay'
  rec.update(status='PASS_ALL_SIX_SELECTED',after_inputs=after,inputs_unchanged=True,semantic_gate_count=sum(len(j['semantic_gates'])for j in rec['jobs']))
 except BaseException as exc:
  rec['status']='FAIL';rec['exception']=repr(exc);rec['traceback']=traceback.format_exc()
  dump(out/'actual.json',rec);raise
 dump(out/'actual.json',rec);print(rec['status'],rec['semantic_gate_count'],flush=True)
if __name__=='__main__':main()

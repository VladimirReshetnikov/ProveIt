#!/usr/bin/env python3
"""Publish only the explicit frozen two-unit additive snapshot to a fresh external packet."""
from pathlib import Path
import argparse,hashlib,json,re,ast,difflib
B=Path('/tmp/zfc-source-rotation244-publication-additive')
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
Z=Path('Computability/BusyBeaver/Research/ZFC');L=Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC')
INPUT_SHA='65b7adc631f8969d29085063f327f89062be3abc9c26efd9c919cdedb0cb71fc'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def d(p):return dict(path=str(p),sha256=sha(p))
def need(x,msg):
 if not x:raise RuntimeError(msg)
def load(p):return json.loads(Path(p).read_text())
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True);a=p.parse_args();out=a.output.resolve()
need(not out.exists() and not out.is_relative_to(ROOT) and not out.is_relative_to(B),'Fresh external packet required')
need(sha(B/'inputs.json')==INPUT_SHA,'Changed explicit snapshot');plan=load(B/'inputs.json');tracked={};cooked={};actual={}
def pin(path,h):
 path=Path(path).resolve();need(sha(path)==h,'Changed '+str(path));need(str(path) not in tracked or tracked[str(path)]==h,'Conflicting identity');tracked[str(path)]=h
for u in plan['units']:
 base=Path(u['base']);v=u['verification'];pin(v['path'],v['sha256']);r=load(v['path']);n=u['probes'];k=u['callers']
 need(r['status']=='PASS' and not r['prepare_only'] and (r['named_axiom_probes'],r['callers'],r['warnings'])==(n,k,0),'Actual status/census')
 need(r['before']==r['after'] and r['all_input_provider_postchecks'] and r['all_fresh_objects_unchanged_after_audit'] and r['only_standard_axioms'],'Actual postchecks')
 for path,h in r['before'].items():pin(path,h)
 need(sum(c['output'].count('warning:') for c in r['commands'])==0,'Actual raw warnings')
 need(r['shared_timeout_seconds']==120 and r['memory_mebibytes']==4096 and r['LEAN_NUM_THREADS']=='1' and r['global_option_overrides']==[],'Resource defaults')
 need(not any(r[x] for x in ['compiler_version_query_performed','dependency_build','downloads']),'Unexpected side execution')
 need(len(r['reused_modules'])==r['exact_project_prerequisite_count']==u['projects'],'Project census')
 for q in r['reused_modules']:
  for x in ['source','object']:pin(q[x],q[x+'_sha256']);need(r['before'].get(q[x])==q[x+'_sha256'],'Recorded project input')
 expected_first={q['module']:(str(Path(q['object']).resolve()),q['object_sha256']) for q in r['reused_modules']+r['toolchain_providers']}
 need(len(expected_first)==u['projects']+1 and {q['module'] for q in r['toolchain_providers']}=={'Init'},'Exact project/Init boundary')
 need({q['module']:(str(Path(q['actual_first']).resolve()),q['sha256']) for q in r['actual_first_providers']}==expected_first,'Actual first providers')
 need(len(r['actual_first_providers'])==len(expected_first),'No duplicate actual providers')
 need(sorted(r['exact_project_import_closure'])==sorted(q['module'] for q in r['reused_modules']),'Recorded exact closure')
 for q in r['provider_evidence']:pin(q['path'],q['sha256'])
 need([c['label'] for c in r['commands']]==['source','audit'],'Sequential proof pair')
 for i,c in enumerate(r['commands']):
  need(c['exit_code']==0 and not c['timed_out'] and c['interrupted'] is None,'Failed command')
  need(c['command'][:3]==[r['compiler']['path'],'-j1','-M4096'] and c['command'][-1]==r[['source','audit'][i]]['snapshot'],'Command selection')
  pin(c['log'],c['log_sha256']);need(Path(c['log']).read_text()==c['output'],'Raw log mismatch')
 need(sum(c['seconds'] for c in r['commands'])<120,'Shared deadline')
 for x in ['source','audit']:pin(r[x]['path'],r[x]['sha256']);pin(r[x]['snapshot'],r[x]['sha256'])
 need(d(r['source']['path'])==u['source'] and d(r['audit']['path'])==u['audit'] and r['boundary']==u['boundary'],'Exact source/audit/boundary identities')
 f=r['fresh_modules'];need(len(f)==1,'Single fresh target');f=f[0];pin(f['path'],f['sha256'])
 need(f['module']=='BusyBeaver.ZFC.'+u['module'] and f['source_sha256']==r['source']['sha256'],'Fresh source binding')
 need(r['source_object_recorded_before_audit'] and r['source_pass_object']==dict(f,source_command_index=0) and r['fresh_first_provider_before_audit']=={x:f[x] for x in ['module','path','sha256']},'Pre-audit capture')
 names=re.findall(r'^#print axioms (\S+)$',Path(r['audit']['path']).read_text(),re.M)
 need(names==[q['name'] for q in r['axiom_reports']] and len(names)==n and len(re.findall(r'^example\b',Path(r['audit']['path']).read_text(),re.M))==k,'Typed audit census')
 raw_reports=re.findall(r"^'([^\n]+)'[ \t]+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",r['commands'][1]['output'],re.M)
 need([dict(name=name,axioms=sorted({x.strip() for x in ax.split(',') if x.strip()})) for name,ax in raw_reports]==r['axiom_reports'],'Raw axiom reports')
 need(all(set(q['axioms'])<={'propext','Quot.sound','Classical.choice'} for q in r['axiom_reports']),'Axiom scope')
 pin(u['review']['path'],u['review']['sha256']);rv=load(u['review']['path'])
 need(rv['status']=='EXISTING_ACTUAL_EVIDENCE_REVIEW_PASS' and rv['findings']==[] and rv['verification']==v,'Exact existing review')
 for x in ['source','audit']:need(rv[x]==d(r[x]['path']),'Reviewed proof identity')
 need(rv['guard']==u['guard'],'Reviewed guard identity');pin(rv['reviewer_source']['path'],rv['reviewer_source']['sha256'])
 need(r['before'].get(u['guard']['path'])==u['guard']['sha256'],'Executed guard exact')
 pin(u['guard']['path'],u['guard']['sha256'])
 selected={q['path']:q['sha256'] for q in u['files']};need(len(selected)==len(u['files']),'Unique snapshot paths')
 for q in [v,u['source'],u['audit'],u['guard'],u['boundary'],u['review'],rv['reviewer_source']]+u['preparations']:
  need(selected.get(q['path'])==q['sha256'],'Required evidence in explicit snapshot')
 for q in r['commands']:need(selected.get(q['log'])==q['log_sha256'],'Raw actual log preserved')
 for x in ['source','audit']:need(selected.get(r[x]['snapshot'])==r[x]['sha256'],'Actual proof snapshot preserved')
 for q in u['files']:
  rel=Path(q['relative']);need(not rel.is_absolute() and '..' not in rel.parts and not any(x in {'cache','__pycache__','.lake','.git'} for x in rel.parts) and rel.suffix not in {'.olean','.ilean','.c','.o','.so','.pyc'} and not Path(q['path']).is_symlink(),'No compiled/symlinked cache')
  need(Path(q['path']).resolve()==base/q['relative'],'Snapshot path binding');pin(q['path'],q['sha256']);Path(q['path']).read_bytes().decode('utf-8')
 for pd in u['preparations']:
  pin(pd['path'],pd['sha256']);pr=load(pd['path']);need(pr['status']=='PREPARED_NOT_BUILT' and pr['commands']==pr['fresh_modules']==[] and pr['before']==pr['after'] and pr['all_input_provider_postchecks'],'Preparation scope')
  for path,h in pr['before'].items():pin(path,h)
 raw=Path(u['guard']['path']).read_text();s=raw
 changes=[("HERE=Path('"+str(base)+"')",'HERE=Path(__file__).resolve().parent\nREPO=HERE.parents[3]'),("default=HERE/'"+str(Path(u['source']['path']).relative_to(base))+"'","default=REPO/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/"+u['module']+".lean'"),("default=HERE/'Audit.lean'","default=HERE/'"+u['stem']+"_audit.lean'"),("default=HERE/'"+str(Path(u['boundary']['path']).relative_to(base))+"'","default=HERE/'source-rotation244-formal/"+u['slug']+"/"+Path(u['boundary']['path']).name+"'")]
 for before,after in changes:need(s.count(before)==1,'Default occurrence');s=s.replace(before,after)
 inverse=s
 for before,after in reversed(changes):need(inverse.count(after)==1,'Default inverse occurrence');inverse=inverse.replace(after,before)
 need(inverse==raw,'Only path defaults may differ');ast.parse(s);cooked[u['slug']]=(s,''.join(difflib.unified_diff(raw.splitlines(True),s.splitlines(True),fromfile='executed-check.py',tofile='maintained-check.py')));actual[u['slug']]=v
bridge=plan['units'][0];need(bridge['module']=='SourceRotation244','Concrete source first')
failure=plan['failed_source_attempt'];pin(failure['path'],failure['sha256']);bad=load(failure['path'])
need(bad['status']=='FAIL' and len(bad['commands'])==1 and bad['fresh_modules']==[] and bad['before']==bad['after'] and bad['all_input_provider_postchecks'],'Preserved failed source attempt')
for path,h in bad['before'].items():pin(path,h)
for c in bad['commands']:
 pin(c['log'],c['log_sha256']);need(Path(c['log']).read_text()==c['output'] and c['exit_code']!=0 and c['output'].count('error:')==1 and 'Tactic `rewrite` failed' in c['output'],'Exact failed source log')
oldsrc=Path(bad['source']['path']).read_text();newsrc=Path(bridge['source']['path']).read_text()
need(newsrc==oldsrc.replace('      rw [hn]\n','      dsimp only [ofProgram]\n      rw [hn]\n') and oldsrc.count('      rw [hn]\n')==1,'Only one explicit unfolding repair')
need(bad['audit']['sha256']==bridge['audit']['sha256'],'Audit unchanged across repair')
selected={q['path']:q['sha256'] for q in bridge['files']}
for q in [failure]+plan['required_failure_history']:
 pin(q['path'],q['sha256']);need(selected.get(q['path'])==q['sha256'],'Failed lineage preserved in explicit snapshot')
for q in plan['prior_publication_provenance']:
 pin(q['path'],q['sha256'])
for key in ['note','prior_note','readme_proposal']:pin(plan[key]['path'],plan[key]['sha256'])
need((ROOT/Z/'source_rotation244.md').read_bytes()==Path(plan['prior_note']['path']).read_bytes(),'Exact prior maintained note before replacement')
# No source-tree glob occurs here: only the immutable completed-unit file list is used.
out.mkdir();files=[];targets=set()
def put(target,data,origin):
 need(not target.is_absolute() and '..' not in target.parts and str(target) not in targets,'Unsafe/duplicate target');targets.add(str(target))
 dst=out/'files'/target;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(data)
 files.append(dict(path=str(target),packet_path=str(dst),sha256=sha(dst),bytes=len(data),origin=origin))
def copy(src,target):put(target,Path(src).read_bytes(),str(src))
for u in plan['units']:
 base=Path(u['base']);arc=Z/'source-rotation244-formal'/u['slug']
 for q in u['files']:copy(q['path'],arc/q['relative'])
 copy(u['source']['path'],L/(u['module']+'.lean'));copy(u['audit']['path'],Z/(u['stem']+'_audit.lean'))
 text,delta=cooked[u['slug']];put(Z/('check_'+u['stem']+'.py'),text.encode(),'Maintained path defaults only');put(arc/'publication-defaults.diff',delta.encode(),'Exact default-only inverse')
 copy(u['verification']['path'],Z/'results'/('source-rotation244-'+u['slug']+'-verification.json'))
copy(plan['note']['path'],Z/'source_rotation244.md')
pub=Z/'source-rotation244-formal/publication/additive-five'
copy(B/'inputs.json',pub/'inputs.json');copy(__file__,pub/'build_packet.py')
copy(plan['prior_note']['path'],pub/'history/three-unit-note.md');copy(plan['readme_proposal']['path'],pub/'README-append.txt')
for q in plan['prior_publication_provenance']:copy(q['path'],pub/'prerequisites'/q['relative'])
need(all(sha(path)==h for path,h in tracked.items()),'Inputs changed during metadata publication')
manifest=dict(status='TWO_ADDITIONAL_COMPLETED_SOURCE_ROTATION_UNITS_PACKET',proof_execution=False,writer=d(__file__),inputs=d(B/'inputs.json'),actual_records=actual,probes=16,callers=19,total_five_units_probes=34,total_five_units_callers=40,warnings=0,prior_three_unit_packet_unchanged=True,scope='Concrete arbitrary-register source equivalence and external logical-seed native/ZF/ZFC calibration. Binary runtime/blank startup and internal PA remain separate.',files=files)
(out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');(out/'map.json').write_text(json.dumps(files,indent=2)+'\n')
print(json.dumps(dict(files=len(files),manifest=d(out/'manifest.json'),map=d(out/'map.json')),indent=2))

"""Fresh-check internal successor/append execution and its stored15/20audit.

Explicit successful Tick/Run and WordLaws records supply the exact24-import
source/object closure. Pinned prebuilt external providers are identified, not
rebuilt or independently attested as a whole. No compiler/scheduler/PA
consistency endpoint is checked by this runner.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,time,tempfile
SOURCE=Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticCommandExecution254.lean')
AUDIT=Path('Computability/BusyBeaver/Research/ZFC/arithmetic_command_execution254_audit.lean')
SOURCE_HASH='fe5fe311d00a1fd6f21dd8d14bb71fb13419db746329bf65dc67aed09928a6ee'
AUDIT_HASH='da4b895c0ed0ad4dec1aa87dc01d08e9f6dc8177549b7cecac3418a594a19a76'
NAME='BusyBeaver.ZFC.ArithmeticCommandExecution254';PREFIX='SetTheory.BusyBeaver.ZFC.ArithmeticCommandExecution254.'
PROBES=[PREFIX+n for n in ('extend_defined','extend_live','tick_extend_succ','tick_extend_active','run_eq_of_stopped_le','stopped_runs_eq','terminal_eq_run','run_one_succ','terminal_succ','eval_succ','paired_or_stopped','stopped_pair','terminal_append','eval_append','eval_append_eq_zero')]
PROVIDERS={'Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Tactic.Ring','Foundation.FirstOrder.Arithmetic.HFS.PRF','Foundation.FirstOrder.Arithmetic.HFS.Seq'}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
_owned_record=None
def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--repo',type=Path);p.add_argument('--dependency-root',type=Path,required=True)
 p.add_argument('--run-evidence',type=Path,required=True);p.add_argument('--word-laws-evidence',type=Path,required=True)
 p.add_argument('--run-cache',type=Path);p.add_argument('--word-laws-cache',type=Path)
 p.add_argument('--source',type=Path);p.add_argument('--audit',type=Path);p.add_argument('--lean',type=Path)
 p.add_argument('--library-path',type=Path,action='append',default=[])
 p.add_argument('--output',type=Path);p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
 ROOT=a.repo.resolve()if a.repo else next((q for q in Path(__file__).resolve().parents if(q/'.git').exists()),None)
 if ROOT is None:p.error('Pass --repo outside a checkout.')
 DEP=a.dependency_root.resolve()
 if not __debug__:p.error('Keep assertions enabled.')
 ep=a.run_evidence.resolve();wp=a.word_laws_evidence.resolve();e=json.loads(ep.read_text());w=json.loads(wp.read_text())
 assert e['status']==w['status']=='PASS'and e['named_axiom_probes']==25 and e['callers']==30 and w['named_axiom_probes']==6 and w['callers']==7
 assert e['only_standard_axioms']and w['only_standard_axioms']and(e.get('all_inputs_sources_objects_providers_unchanged')is True or e.get('all_input_provider_postchecks')is True)and e['all_fresh_objects_unchanged_after_audit']and w['fresh_object_unchanged_after_check']
 for flag in ['all_input_provider_identities_unchanged_after_check','all_reused_project_objects_match_evidence_after_check','dependency_pins_and_clean_status_unchanged_after_check']:assert w.get(flag)is True
 rows={q['module']:dict(q)for q in e['reused_modules']};alternatives=[]
 for q in e['fresh_modules']:
  rows[q['module']]={'module':q['module'],'source':str(ROOT/'Computability/BusyBeaver/Lean'/Path(q['module'].replace('.','/')).with_suffix('.lean')),'source_sha256':q['source_sha256'],'object':q['path'],'object_sha256':q['sha256']}
 for mod,q in rows.items():
  assert mod=='FirstOrder.Fol'or mod.startswith('BusyBeaver.ZFC.')
  directory=Path('Logic/FirstOrder/Lean')if mod=='FirstOrder.Fol'else Path('Computability/BusyBeaver/Lean')
  q['source']=str(ROOT/directory/Path(mod.replace('.','/')).with_suffix('.lean'))
  if a.run_cache:q['object']=str(a.run_cache.resolve()/Path(mod.replace('.','/')).with_suffix('.olean'))
 for q in w['reused_project']:
  old=rows.get(q['module']);new={'module':q['module'],'source':str(ROOT/q['path']),'source_sha256':q['source_sha256'],'object':str(a.word_laws_cache.resolve()/Path(q['module'].replace('.','/')).with_suffix('.olean'))if a.word_laws_cache else q['olean'],'object_sha256':q['olean_sha256']}
  if old:
   assert old['source_sha256']==new['source_sha256']
   if old['object_sha256']!=new['object_sha256']:
    assert q['module']=='BusyBeaver.ZFC.ArithmeticCantor';assert H(new['source'])==new['source_sha256']and H(new['object'])==new['object_sha256'];alternatives.append({'selected':old,'same_source_alternative':new})
  else:rows[q['module']]=new
 q=w['module_object'];s=w['source'];rows['BusyBeaver.ZFC.ArithmeticCommandWordLaws254']={'module':'BusyBeaver.ZFC.ArithmeticCommandWordLaws254','source':str(ROOT/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticCommandWordLaws254.lean'),'source_sha256':s['sha256'],'object':str(a.word_laws_cache.resolve()/'BusyBeaver/ZFC/ArithmeticCommandWordLaws254.olean')if a.word_laws_cache else q['path'],'object_sha256':q['sha256']}
 assert len(rows)==24
 for q in rows.values():assert H(q['source'])==q['source_sha256']and H(q['object'])==q['object_sha256']
 helper=ROOT/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';spec=importlib.util.spec_from_file_location('exec_cantor_helpers',helper);b=importlib.util.module_from_spec(spec);spec.loader.exec_module(b)
 known=set(rows);external=set()
 for q in rows.values():external|={n for n in b.lean_imports(Path(q['source']).read_text())if n not in known and not n.startswith(('Init','Std','Lean'))}
 assert external=={'Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Tactic.Ring','Foundation.FirstOrder.Arithmetic.HFS.PRF'}
 libs,deps=b.dependency_libraries(DEP,a.library_path)
 for k in ['Foundation','Mathlib']:assert deps[k]['pin']==e['dependencies'][k]['pin']==w['dependencies'][k]['pin']
 assert deps['lake_manifest_sha256']==e['dependencies']['lake_manifest_sha256']==w['dependencies']['lake_manifest_sha256']
 oldproviders=e['providers']if isinstance(e['providers'],dict)else{q['module']:{'path':q['object'],'sha256':q['object_sha256'],'source':q['source'],'source_sha256':q['source_sha256']}for q in e['providers']}
 assert set(oldproviders)==set(w['providers'])==PROVIDERS
 providers={}
 for name,q in oldproviders.items():
  rel=Path(name.replace('.','/'));actual=next((x/rel.with_suffix('.olean')for x in libs if(x/rel.with_suffix('.olean')).is_file()),None)
  dep='Foundation'if name.startswith('Foundation.')else'Mathlib';provider_source=Path(deps[dep]['path'])/rel.with_suffix('.lean')
  assert actual is not None and H(actual)==q['sha256']and provider_source.is_file()
  if 'source_sha256'in q:assert H(provider_source)==q['source_sha256']
  assert H(actual)==w['providers'][name]['sha256']
  if 'source_sha256'in w['providers'][name]:assert H(provider_source)==w['providers'][name]['source_sha256']
  for prior in (e,w):
   recorded=prior['dependencies']['providers'].get(name)
   if recorded:assert H(actual)==recorded['sha256']
  providers[name]=dict(q,actual_first=str(actual.resolve()),source=str(provider_source.resolve()),source_sha256=H(provider_source))
 lean=a.lean.resolve()if a.lean else Path(e['compiler']['path']).resolve();assert lean.is_absolute()and lean.is_file()and lean.name.lower()not in {'elan','elan.exe'};assert H(lean)==e['compiler']['sha256']==w['compiler']['sha256']
 src=a.source.resolve()if a.source else ROOT/SOURCE;audit=a.audit.resolve()if a.audit else ROOT/AUDIT
 assert a.source is not None or H(src)==SOURCE_HASH
 assert a.audit is not None or H(audit)==AUDIT_HASH
 assert b.lean_imports(src.read_text())==['BusyBeaver.ZFC.ArithmeticCommandRun254','BusyBeaver.ZFC.ArithmeticCommandWordLaws254']and b.lean_imports(audit.read_text())==[NAME]
 probes=re.findall(r'^#print axioms (.+)$',audit.read_text(),re.M);assert probes==PROBES and len(re.findall(r'^example\b',audit.read_text(),re.M))==20
 work=a.output.resolve()if a.output else Path(tempfile.mkdtemp(prefix='zfc-command-execution-'));assert not work.is_relative_to(ROOT)and not work.is_relative_to(DEP);assert not work.exists()or not any(work.iterdir());work.mkdir(parents=True,exist_ok=True);cache=work/'cache';cache.mkdir()
 for q in rows.values():
  dest=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(q['object'])
 inputs=[Path(__file__),helper,src,audit,ep,wp,lean,DEP/'lake-manifest.json']+[Path(q[k])for q in rows.values()for k in ['source','object']]+[Path(q['actual_first'])for q in providers.values()]
 for q in alternatives:inputs.append(Path(q['same_source_alternative']['object']))
 for q in providers.values():
  if'source'in q:inputs.append(Path(q['source']))
 inputs=list(dict.fromkeys(x.resolve()for x in inputs));before={str(x):H(x)for x in inputs}
 snap=work/'sources'/Path(NAME.replace('.','/')).with_suffix('.lean');snap.parent.mkdir(parents=True);shutil.copyfile(src,snap);asnap=work/'Audit.lean';shutil.copyfile(audit,asnap)
 d={'status':'PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING','scope':'Allinternal IΣ1 successor and append command execution; no compiler block/scheduler/PA consistency endpoint.','source':{'path':str(src),'sha256':H(src),'snapshot':str(snap),'explicit_override':a.source is not None},'audit':{'path':str(audit),'sha256':H(audit),'snapshot':str(asnap),'explicit_override':a.audit is not None},'reused_modules':list(rows.values()),'reused_count':24,'same_source_object_alternatives':alternatives,'providers':providers,'compiler':dict(e['compiler'],path=str(lean)),'dependencies':deps,'prerequisites':[str(ep),str(wp)],'commands':[],'before':before,'LEAN_PATH':os.pathsep.join(map(str,[cache,*libs])),'dependency_build':False,'downloads':False}
 def save():
  global _owned_record
  target=work/'verification.json';target.write_text(json.dumps(d,indent=2)+'\n');_owned_record=target
 save()
 def provider_postchecks():
  for name,q in providers.items():
   rel=Path(name.replace('.','/')).with_suffix('.olean');actual=next((x/rel for x in libs if(x/rel).is_file()),None)
   assert actual is not None and str(actual.resolve())==q['actual_first']and H(actual)==q['sha256']and H(q['source'])==q['source_sha256']
  _,after_deps=b.dependency_libraries(DEP,a.library_path);assert deps==after_deps
 if a.prepare_only:
  assert before=={p:H(p)for p in before};provider_postchecks();d['all_preparation_inputs_unchanged']=True;d['all_provider_postchecks']=True;save();print(work/'verification.json');return
 assert subprocess.check_output([str(lean),'--version'],text=True).strip()==e['compiler']['version']
 env=dict(os.environ,LEAN_PATH=d['LEAN_PATH'],LEAN_NUM_THREADS='1')
 def run(label,cmd):
  t=time.monotonic();r=subprocess.run(cmd,cwd=work,env=env,capture_output=True,text=True);out=r.stdout+r.stderr;(work/(label+'.log')).write_text(out);d['commands'].append({'label':label,'command':cmd,'exit_code':r.returncode,'seconds':round(time.monotonic()-t,6),'output':out});save();print(label,r.returncode,d['commands'][-1]['seconds'],flush=True)
  if r.returncode or'sorryAx'in out or"declaration uses 'sorry'"in out:d.update(status='FAIL',error=label+' failed');save();raise RuntimeError(out)
  return out
 obj=cache/Path(NAME.replace('.','/')).with_suffix('.olean');run('source',[str(lean),'-M4096','--root='+str(work/'sources'),'-o',str(obj),str(snap)]);oh=H(obj);d['object_immediately_after_source']={'path':str(obj),'sha256':oh};save();out=run('audit',[str(lean),'-M4096',str(asnap)])
 reports=[]
 for n,block in re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)",out,re.S):
  ax=[x.strip()for x in block.split(',')if x.strip()];assert set(ax)<={'propext','Classical.choice','Quot.sound'};reports.append({'theorem':n,'axioms':ax})
 assert[q['theorem']for q in reports]==probes
 after={p:H(p)for p in before};assert before==after and H(obj)==oh and H(snap)==H(src)and H(asnap)==H(audit)
 provider_postchecks()
 d.update(status='PASS',after=after,all_sources_objects_providers_unchanged=True,all_provider_postchecks=True,module_object={'path':str(obj),'sha256':oh},named_axiom_probes=15,callers=20,axiom_reports=reports,only_standard_axioms=True,warnings=sum(q['output'].count('warning:')for q in d['commands']));save();print(work/'verification.json')
if __name__=='__main__':
 try:main()
 except Exception as error:
  if _owned_record is not None:
   data=json.loads(_owned_record.read_text());data.update(status='FAIL',error=str(error));_owned_record.write_text(json.dumps(data,indent=2)+'\n')
  raise

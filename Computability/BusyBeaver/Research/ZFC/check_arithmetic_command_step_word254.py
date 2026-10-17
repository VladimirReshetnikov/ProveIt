"""Fresh-check the local raw-rest/working-effect bridge and its stored audit.

Requires explicit successful command-step and WordLaws evidence, reconstructs
the19-import selected project closure, and identifies the actual first pinned
external providers. No word executor/scheduler/compiler endpoint is asserted.
"""
from pathlib import Path
import argparse,importlib.util,json,hashlib,os,re,subprocess,shutil,time,tempfile
SOURCE=Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticCommandStepWord254.lean')
AUDIT=Path('Computability/BusyBeaver/Research/ZFC/arithmetic_command_step_word254_audit.lean')
SOURCE_HASH='f027ebdd4726d3dd98a49a3e10a5c86a9cd9331e3866131fc7358f2ee4658b1d'
AUDIT_HASH='2268a25abe3cd77a1e0d81a64ad3a2ac0826c655ab3d03441daf6f328b397dbd'
MODULE='BusyBeaver.ZFC.ArithmeticCommandStepWord254'
PREFIX='SetTheory.BusyBeaver.ZFC.ArithmeticCommandStepWord254.'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--repo',type=Path);p.add_argument('--dependency-root',type=Path,required=True)
 p.add_argument('--step-evidence',type=Path,required=True);p.add_argument('--word-evidence',type=Path,required=True,help='successful WordLaws record containing its17-source matched import overlay')
 p.add_argument('--step-cache',type=Path);p.add_argument('--word-cache',type=Path)
 p.add_argument('--source',type=Path);p.add_argument('--audit',type=Path);p.add_argument('--lean',type=Path)
 p.add_argument('--library-path',type=Path,action='append',default=[])
 p.add_argument('--output',type=Path);p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
 if not __debug__:p.error('Keep assertions enabled; do not use -O.')
 ROOT=a.repo.resolve() if a.repo else next((q for q in Path(__file__).resolve().parents if(q/'.git').exists()),None)
 if ROOT is None:p.error('Pass --repo outside a checkout.')
 DEP=a.dependency_root.resolve()
 ep=a.step_evidence.resolve();wp=a.word_evidence.resolve();e=json.loads(ep.read_text());w=json.loads(wp.read_text())
 assert e['status']==w['status']=='PASS' and e['all_inputs_objects_unchanged'] and w['fresh_object_unchanged_after_check']
 assert w.get('named_axiom_probes')==6 and w.get('callers')==7 and w.get('only_standard_axioms')is True
 for flag in ['all_input_provider_identities_unchanged_after_check','all_reused_project_objects_match_evidence_after_check','fresh_object_unchanged_after_check','dependency_pins_and_clean_status_unchanged_after_check']:assert w.get(flag)is True
 assert e['named_axiom_probes']==17 and e['callers']==19 and e['only_standard_axioms'] is True
 assert e['source']['sha256']=='ca0a9533e82d3de393459354269f49b756597b45305760fb284002eae1ea4d29'
 rows={q['module']:dict(q) for q in e['reused']};adds=[];alternative=[]
 for module,q in rows.items():
  assert module=='FirstOrder.Fol'or module.startswith('BusyBeaver.ZFC.')
  directory=Path('Logic/FirstOrder/Lean')if module=='FirstOrder.Fol'else Path('Computability/BusyBeaver/Lean')
  q['source']=str(ROOT/directory/Path(module.replace('.','/')).with_suffix('.lean'))
 if a.step_cache:
  for q in rows.values():q['object']=str(a.step_cache.resolve()/Path(q['module'].replace('.','/')).with_suffix('.olean'))
 for q in w['reused_project']:
  if q['module'] not in {'BusyBeaver.ZFC.EnumSafeStart254','BusyBeaver.ZFC.EnumStackBarrier254','BusyBeaver.ZFC.CommandWord254','BusyBeaver.ZFC.ArithmeticCommandWord254'}:continue
  new={'module':q['module'],'source':str(ROOT/q['path']),'source_sha256':q['source_sha256'],'object':str(a.word_cache.resolve()/Path(q['module'].replace('.','/')).with_suffix('.olean'))if a.word_cache else q['olean'],'object_sha256':q['olean_sha256'],'evidence':str(wp)};rows[q['module']]=new;adds.append(new)
 cq=dict(next(q for q in w['reused_project']if q['module']=='BusyBeaver.ZFC.ArithmeticCantor'))
 if a.word_cache:cq['olean']=str(a.word_cache.resolve()/'BusyBeaver/ZFC/ArithmeticCantor.olean')
 chosen=rows[cq['module']];assert cq['source_sha256']==chosen['source_sha256']
 assert H(cq['olean'])==cq['olean_sha256']
 if cq['olean_sha256']!=chosen['object_sha256']:alternative.append({'module':cq['module'],'chosen_object':chosen['object'],'chosen_sha256':chosen['object_sha256'],'same_source_alternative_object':cq['olean'],'same_source_alternative_sha256':cq['olean_sha256'],'claim':'different checked objects of identical source; no object equality inferred'})
 sf=e['source'];ob=dict(e['module_object'])
 if a.step_cache:ob['path']=str(a.step_cache.resolve()/'BusyBeaver/ZFC/ArithmeticCommandStep254.olean')
 rows['BusyBeaver.ZFC.ArithmeticCommandStep254']={'module':'BusyBeaver.ZFC.ArithmeticCommandStep254','source':str(ROOT/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticCommandStep254.lean'),'source_sha256':sf['sha256'],'object':ob['path'],'object_sha256':ob['sha256'],'evidence':str(ep)}
 for q in rows.values():assert H(q['source'])==q['source_sha256']and H(q['object'])==q['object_sha256']
 src=a.source.resolve()if a.source else ROOT/SOURCE;audit=a.audit.resolve()if a.audit else ROOT/AUDIT
 assert a.source is not None or H(src)==SOURCE_HASH
 assert a.audit is not None or H(audit)==AUDIT_HASH
 work=a.output.resolve()if a.output else Path(tempfile.mkdtemp(prefix='zfc-command-step-word-'))
 assert not work.is_relative_to(ROOT)and not work.is_relative_to(DEP)and(not work.exists()or not any(work.iterdir()))
 work.mkdir(parents=True,exist_ok=True);cache=work/'cache';cache.mkdir()
 for q in rows.values():
  dest=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(q['object'])
 helper=ROOT/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py'
 spec=importlib.util.spec_from_file_location('step_word_cantor_helpers',helper);b=importlib.util.module_from_spec(spec);spec.loader.exec_module(b)
 assert b.lean_imports(src.read_text())==['BusyBeaver.ZFC.ArithmeticCommandStep254','BusyBeaver.ZFC.ArithmeticCommandWord254']
 assert b.lean_imports(audit.read_text())==[MODULE]
 assert re.findall(r'^#print axioms (.+)$',audit.read_text(),re.M)==[PREFIX+n for n in ['short_tag_iff','step_replace','step_replace_eq_zero']]
 assert len(re.findall(r'^example\b',audit.read_text(),re.M))==4
 libs,deps=b.dependency_libraries(DEP,a.library_path)
 for key in ['Foundation','Mathlib']:assert deps[key]['pin']==e['dependencies'][key]['pin']==w['dependencies'][key]['pin']
 assert deps['lake_manifest_sha256']==e['dependencies']['lake_manifest_sha256']==w['dependencies']['lake_manifest_sha256']
 for name,q in deps['providers'].items():assert q['sha256']==e['dependencies']['providers'][name]['sha256']==w['dependencies']['providers'][name]['sha256']
 lean=a.lean.resolve()if a.lean else Path(e['compiler']['path']).resolve()
 assert lean.is_absolute()and lean.is_file()and lean.name.lower()not in {'elan','elan.exe'}and H(lean)==e['compiler']['sha256']==w['compiler']['sha256']
 known=set(rows);external=set()
 for q in rows.values():external|={n for n in b.lean_imports(Path(q['source']).read_text())if n not in known and not n.startswith(('Init','Std','Lean'))}
 assert len(rows)==19 and external=={'Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Tactic.Ring'}
 inputs=[Path(__file__),helper,src,audit,ep,wp,lean,DEP/'lake-manifest.json']+[Path(q[k])for q in rows.values()for k in ['source','object']]+[Path(q['path'])for q in deps['providers'].values()]
 inputs.append(Path(cq['olean']))
 for name in deps['providers']:
  parent=Path(deps['Foundation']['path'])if name.startswith('Foundation.')else Path(deps['Mathlib']['path'])
  inputs.append(parent/Path(name.replace('.','/')).with_suffix('.lean'))
 inputs=list(dict.fromkeys(x.resolve()for x in inputs));before={str(p):H(p)for p in inputs};snap=work/'sources/BusyBeaver/ZFC/ArithmeticCommandStepWord254.lean';snap.parent.mkdir(parents=True);shutil.copyfile(src,snap);asnap=work/'Audit.lean';shutil.copyfile(audit,asnap)
 d={'status':'RUNNING','scope':'Only all-IOpen raw-rest replacement preserves exact working-state effect; no word execution or scheduler theorem.','source':{'path':str(src),'sha256':H(src),'snapshot':str(snap),'explicit_override':a.source is not None},'audit':{'path':str(audit),'sha256':H(audit),'snapshot':str(asnap),'explicit_override':a.audit is not None},'prerequisites':[str(ep),str(wp)],'reused_modules':list(rows.values()),'reused_count':len(rows),'same_source_object_alternatives':alternative,'before':before,'commands':[],'compiler':dict(e['compiler'],path=str(lean)),'dependencies':deps,'LEAN_PATH':os.pathsep.join(map(str,[cache,*libs])),'dependency_build':False,'downloads':False,'prepare_only':a.prepare_only}
 save=lambda:(work/'verification.json').write_text(json.dumps(d,indent=2)+'\n');save();env=dict(os.environ,LEAN_PATH=d['LEAN_PATH'],LEAN_NUM_THREADS='1')
 if a.prepare_only:
  assert before=={p:H(p)for p in before};d.update(status='PREPARED_NOT_BUILT',all_preparation_inputs_unchanged=True);save();print(work/'verification.json');return
 assert subprocess.check_output([str(lean),'--version'],text=True).strip()==e['compiler']['version']
 def run(label,cmd):
  t=time.monotonic();r=subprocess.run(cmd,cwd=work,env=env,capture_output=True,text=True);out=r.stdout+r.stderr;(work/(label+'.log')).write_text(out);d['commands'].append({'label':label,'command':cmd,'exit_code':r.returncode,'seconds':round(time.monotonic()-t,6),'output':out});save();assert r.returncode==0 and 'sorryAx'not in out and "declaration uses 'sorry'"not in out,out;print(label,d['commands'][-1]['seconds'],flush=True);return out
 obj=cache/'BusyBeaver/ZFC/ArithmeticCommandStepWord254.olean'
 run('source',[str(lean),'--root='+str(work/'sources'),'-o',str(obj),str(snap)]);oh=H(obj);d['object_after_source']={'path':str(obj),'sha256':oh};save();out=run('audit',[str(lean),str(asnap)])
 reports=[]
 for n,block in re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)",out,re.S):
  ax=[x.strip()for x in block.split(',')if x.strip()];assert set(ax)<={'propext','Classical.choice','Quot.sound'};reports.append({'theorem':n,'axioms':ax})
 assert[n['theorem']for n in reports]==re.findall(r'^#print axioms (.+)$',audit.read_text(),re.M)
 after={p:H(p)for p in before};assert after==before and H(obj)==oh and H(snap)==H(src)and H(asnap)==H(audit)
 for name,q in deps['providers'].items():
  rel=Path(name.replace('.','/')).with_suffix('.olean');actual=next((lib/rel for lib in libs if(lib/rel).is_file()),None)
  assert actual is not None and str(actual.resolve())==str(Path(q['path']).resolve())and H(actual)==q['sha256']
 for key in ['Foundation','Mathlib']:
  q=deps[key];assert b.git(Path(q['path']),'rev-parse','HEAD')==q['pin']and not b.git(Path(q['path']),'status','--porcelain','--untracked-files=no')
 d.update(status='PASS',after=after,all_sources_objects_providers_unchanged=True,module_object={'path':str(obj),'sha256':oh},named_axiom_probes=len(reports),callers=len(re.findall(r'^example\b',audit.read_text(),re.M)),axiom_reports=reports,only_standard_axioms=True,warnings=sum(q['output'].count('warning:')for q in d['commands']));save();print(work/'verification.json')
if __name__=='__main__':
 try:main()
 except Exception as error:
  import sys
  if '--output' in sys.argv:
   target=Path(sys.argv[sys.argv.index('--output')+1])/'verification.json'
   if target.is_file():
    data=json.loads(target.read_text());data.update(status='FAIL',error=str(error));target.write_text(json.dumps(data,indent=2)+'\n')
  raise

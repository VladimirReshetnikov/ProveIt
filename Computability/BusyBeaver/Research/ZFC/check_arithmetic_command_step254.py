"""Fresh-check the exact one-command arithmetic transition and stored audit.

Explicit native169+ and five-arithmetic History evidence supply only the
14transitive source/object-matched imports actually required here. Existing
pinned external caches are identified/reused, never rebuilt/downloaded.
This is not a represented word executor or internal PA consistency endpoint.
"""
from pathlib import Path
import argparse,importlib.util,json,os,re,shutil,subprocess,tempfile,time
SOURCE=Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticCommandStep254.lean')
AUDIT=Path('Computability/BusyBeaver/Research/ZFC/arithmetic_command_step254_audit.lean')
SOURCE_HASH='ca0a9533e82d3de393459354269f49b756597b45305760fb284002eae1ea4d29'
AUDIT_HASH='3b13b808068d4d9c63e07fba3798ef06e06bb3edb6dad3aee8377738b6d5ef8d'
NAME='BusyBeaver.ZFC.ArithmeticCommandStep254'
PREFIX='SetTheory.BusyBeaver.ZFC.ArithmeticCommandStep254.'
PROBES=('state_defined','someState_defined','gate_defined','axStack_defined','effect_defined','step_defined','stepValue_mp','stepValue_drop','stepValue_nip','stepValue_ax','effectValue_eq_zero_iff','stepValue_eq_zero_iff','stateValue_nat','someState_nat','gateValue_nat','axStackValue_nat','stepValue_pack_nat')
ARITH={'ArithmeticCantor','ArithmeticCode254','ArithmeticTemplates254'}
def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--repo',type=Path);p.add_argument('--dependency-root',type=Path,required=True)
 p.add_argument('--core-evidence',type=Path,required=True);p.add_argument('--history-evidence',type=Path,required=True)
 p.add_argument('--core-cache',type=Path);p.add_argument('--history-cache',type=Path)
 p.add_argument('--source',type=Path);p.add_argument('--audit',type=Path)
 p.add_argument('--lean',type=Path);p.add_argument('--library-path',type=Path,action='append',default=[])
 p.add_argument('--output',type=Path);p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
 ROOT=a.repo.resolve() if a.repo else next((q for q in Path(__file__).resolve().parents if(q/'.git').exists()),None)
 if ROOT is None:p.error('Pass --repo outside a checkout.')
 DEP=a.dependency_root.resolve()
 LEAN=a.lean.resolve() if a.lean else (Path(os.environ.get('ELAN_HOME',str(Path.home()/'.elan')))/'toolchains/leanprover--lean4---v4.32.0/bin'/('lean.exe'if os.name=='nt'else'lean')).resolve()
 if not __debug__:p.error('Assertions must remain enabled.')
 helper=ROOT/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py'
 spec=importlib.util.spec_from_file_location('command_step_helpers',helper);b=importlib.util.module_from_spec(spec);spec.loader.exec_module(b)
 H=lambda q:b.digest(Path(q))
 corepath=a.core_evidence.resolve();histpath=a.history_evidence.resolve()
 core=json.loads(corepath.read_text());hist=json.loads(histpath.read_text());rows={q['module']:q for q in core['source_closure']}
 b.fail(core.get('audit',{}).get('exit_code')==0 and bool(core.get('fresh_checks')) and all(q.get('exit_code')==0 for q in core['fresh_checks']),'Native source fresh checks/audit did not pass.')
 b.fail(core['status'].startswith('PASS') and core['units']>=169 and core['all_object_identities_unchanged_after_check'] and core['all_source_identities_unchanged_after_check'],'Expected native169 closure.')
 b.fail(hist.get('total_named_axiom_probes')==151 and hist.get('total_callers')==164,'Unexpected History151/164 contract.')
 b.fail(hist['status']=='PASS' and hist['only_standard_axioms'] and hist['all_source_and_reused_object_identities_unchanged_after_check'],'Expected fresh arithmetic evidence.')
 b.fail(LEAN.is_absolute() and LEAN.is_file() and LEAN.name.lower() not in {'elan','elan.exe'},'Use the real absolute4.32 compiler.')
 b.fail(H(LEAN)==core['compiler']['sha256']==hist['compiler_binary_sha256'],'Compiler differs.')
 source=a.source.resolve() if a.source else ROOT/SOURCE;audit=a.audit.resolve() if a.audit else ROOT/AUDIT
 b.fail(a.source is not None or H(source)==SOURCE_HASH,'Maintained source changed; pass reviewed --source.')
 b.fail(a.audit is not None or H(audit)==AUDIT_HASH,'Maintained audit changed; pass reviewed --audit.')
 b.fail(b.lean_imports(source.read_text())==['BusyBeaver.ZFC.ArithmeticTemplates254','BusyBeaver.ZFC.Enum254'],'Unexpected source imports.')
 b.fail(b.lean_imports(audit.read_text())==[NAME],'Unexpected audit imports.')
 b.fail(re.findall(r'^#print axioms (.+)$',audit.read_text(),re.M)==[PREFIX+n for n in PROBES] and len(re.findall(r'^example\b',audit.read_text(),re.M))==19,'Expected exact17/19 audit.')
 corecache=a.core_cache.resolve()if a.core_cache else Path(core['cache']).resolve()
 arithcache=a.history_cache.resolve()if a.history_cache else Path(hist['module_object']['path']).parents[2]
 b.fail(corecache.is_dir() and arithcache.is_dir(),'Missing exact caches; pass relocation paths.')
 work=a.output.resolve() if a.output else Path(tempfile.mkdtemp(prefix='zfc-command-step-check-'))
 b.fail(not work.is_relative_to(ROOT) and not work.is_relative_to(DEP),'Use scratch outside checkouts.')
 b.fail(not work.exists() or not any(work.iterdir()),'Use fresh scratch.');work.mkdir(parents=True,exist_ok=True)
 d={'status':'PREPARING','scope':'New fixed IOpen exact command working-state transition only; no word execution, compiler transport or PA consistency endpoint.','commands':[],'compiler':{'path':str(LEAN),'sha256':H(LEAN),'version':core['compiler']['version']},'core_evidence':{'path':str(corepath),'sha256':H(corepath)},'history_evidence':{'path':str(histpath),'sha256':H(histpath)},'dependency_rebuild':False,'downloads':False}
 save=lambda:(work/'verification.json').write_text(json.dumps(d,indent=2)+'\n')
 try:
  reused=[]
  want={q['module'] for q in hist['reused_core'] if q['module'] not in {'BusyBeaver.ZFC.Code254Proof','BusyBeaver.ZFC.Code254History'}}|{'BusyBeaver.ZFC.Enum254'}
  for name in sorted(want):
   q=rows[name];s=ROOT/q['path'];obj=corecache/Path(name.replace('.','/')).with_suffix('.olean')
   b.fail(H(s)==q['sha256'] and H(obj)==q['olean_sha256'],'Changed native dependency '+name)
   reused.append({'module':name,'source':str(s),'source_sha256':H(s),'object':str(obj.resolve()),'object_sha256':H(obj),'evidence':str(corepath)})
  found={}
  def walk(x):
   if isinstance(x,dict):
    s=x.get('source');obj=x.get('module_object',x.get('object'))
    if isinstance(s,dict) and isinstance(obj,dict) and 'path'in s and 'path'in obj and Path(s['path']).stem in ARITH:found[Path(s['path']).stem]=(s,obj)
    for v in x.values():walk(v)
   elif isinstance(x,list):
    for v in x:walk(v)
  walk(hist);b.fail(set(found)==ARITH,'Missing arithmetic prerequisites.')
  for name,(s,obj) in sorted(found.items()):
   src=ROOT/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'/(name+'.lean');o=arithcache/'BusyBeaver/ZFC'/(name+'.olean')
   b.fail(H(src)==s['sha256'] and H(o)==obj['sha256'],'Changed arithmetic dependency '+name)
   reused.append({'module':'BusyBeaver.ZFC.'+name,'source':str(src),'source_sha256':H(src),'object':str(o),'object_sha256':H(o),'evidence':str(histpath)})
  b.fail(len(reused)==14,'Expected14 exact transitive imports.')
  known={q['module'] for q in reused};external=set()
  for q in reused:
   external|={n for n in b.lean_imports(Path(q['source']).read_text()) if n not in known and not n.startswith(('Init','Std','Lean'))}
  b.fail(external=={'Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Tactic.Ring'},'Unexpected dependency closure '+str(external))
  libs,deps=b.dependency_libraries(DEP,a.library_path)
  for key in ['Foundation','Mathlib']:b.fail(deps[key]['pin']==hist['dependencies'][key]['pin'],'Dependency pin changed.')
  b.fail(deps['lake_manifest_sha256']==hist['dependencies']['lake_manifest_sha256'],'Dependency manifest changed.')
  for n,q in deps['providers'].items():b.fail(q['sha256']==hist['dependencies']['providers'][n]['sha256'],'Actual selected external provider differs.')
  cache=work/'cache';cache.mkdir()
  for q in reused:
   target=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(q['object'])
  inputs=[Path(__file__),helper,source,audit,corepath,histpath,LEAN,DEP/'lake-manifest.json']
  inputs += [Path(q[k])for q in reused for k in ['source','object']]
  inputs += [Path(q['path'])for q in deps['providers'].values()]
  for name in deps['providers']:
   parent=Path(deps['Foundation']['path'])if name.startswith('Foundation.')else Path(deps['Mathlib']['path'])
   inputs.append(parent/Path(name.replace('.','/')).with_suffix('.lean'))
  inputs=list(dict.fromkeys(q.resolve()for q in inputs));before={str(p):H(p)for p in inputs}
  snap=work/'sources'/Path(NAME.replace('.','/')).with_suffix('.lean');snap.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,snap);asnap=work/'Audit.lean';shutil.copyfile(audit,asnap)
  d.update(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',source={'path':str(source),'sha256':H(source),'snapshot':str(snap),'explicit_override':a.source is not None},audit_source={'path':str(audit),'sha256':H(audit),'snapshot':str(asnap),'explicit_override':a.audit is not None},reused=reused,reused_count=len(reused),before=before,dependencies=deps,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])));save()
  if a.prepare_only:
   b.fail(before=={p:H(p)for p in before},'Input changed during preparation.');d['all_preparation_input_identities_unchanged']=True;save();print(work/'verification.json');return
  b.fail(subprocess.check_output([str(LEAN),'--version'],text=True).strip()==core['compiler']['version'],'Wrong real compiler version.')
  env=dict(os.environ,LEAN_PATH=d['LEAN_PATH'],LEAN_NUM_THREADS='1')
  def run(label,cmd):
   t=time.monotonic();r=subprocess.run(cmd,cwd=work,env=env,capture_output=True,text=True);out=r.stdout+r.stderr;(work/(label+'.log')).write_text(out)
   d['commands'].append({'label':label,'command':cmd,'exit_code':r.returncode,'seconds':round(time.monotonic()-t,6),'output':out});save();print(label,r.returncode,d['commands'][-1]['seconds'],flush=True)
   b.fail(r.returncode==0 and 'sorryAx'not in out and "declaration uses 'sorry'"not in out,label+' failed');return out
  obj=cache/Path(NAME.replace('.','/')).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
  run('source',[str(LEAN),'--root='+str(work/'sources'),'-o',str(obj),str(snap)]);oh=H(obj);d['object_immediately_after_source']={'path':str(obj),'sha256':oh};save()
  out=run('audit',[str(LEAN),str(asnap)])
  reports=[]
  for n,block in re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)",out,re.S):
   ax=[x.strip()for x in block.split(',')if x.strip()];b.fail(set(ax)<=b.STANDARD_AXIOMS,'Unexpected axioms.');reports.append({'theorem':n,'axioms':ax})
  expected=re.findall(r'^#print axioms (.+)$',audit.read_text(),re.M);b.fail([q['theorem']for q in reports]==expected,'Axiom audit mismatch.')
  after={p:H(p)for p in before};b.fail(before==after and H(obj)==oh,'Input/fresh object changed.')
  b.fail(H(snap)==H(source) and H(asnap)==H(audit),'Snapshot changed.')
  for name,q in deps['providers'].items():
   rel=Path(name.replace('.','/')).with_suffix('.olean');actual=next((lib/rel for lib in libs if(lib/rel).is_file()),None)
   b.fail(actual is not None and str(actual.resolve())==str(Path(q['path']).resolve()) and H(actual)==q['sha256'],'Actual first external provider changed.')
  for key in ['Foundation','Mathlib']:
   q=deps[key];b.fail(b.git(Path(q['path']),'rev-parse','HEAD')==q['pin'] and not b.git(Path(q['path']),'status','--porcelain','--untracked-files=no'),'Dependency pin/clean state changed.')
  d.update(status='PASS',after=after,module_object={'path':str(obj),'sha256':oh},named_axiom_probes=len(reports),callers=len(re.findall(r'^example\b',audit.read_text(),re.M)),axiom_reports=reports,only_standard_axioms=True,all_inputs_objects_unchanged=True,warnings=sum(q['output'].count('warning:')for q in d['commands']));save();print(work/'verification.json',flush=True)
 except Exception as e:d.update(status='FAIL',error=str(e));save();raise
if __name__=='__main__':main()

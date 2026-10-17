"""Fresh-check the internal history recurrence module and its stored audit.

Reuses an explicit successful five-module ArithmeticHistory record and a
source/object-matched169+ Std core. Pinned prebuilt external providers must be
the actual first objects in the chosen library path and match prior hashes.
No dependencies are rebuilt/downloaded. This is not an internal compiler,
command execution or PA consistency/proof-transport theorem.
"""
from pathlib import Path
import argparse,importlib.util,json,os,re,shutil,subprocess,tempfile,time
SOURCE=Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticHistoryRecurrence254.lean')
AUDIT=Path('Computability/BusyBeaver/Research/ZFC/arithmetic_history_recurrence254_audit.lean')
SOURCE_SHA256='5d2bf146c7bed7d60e8297a911496d1009696bec858edb4f8be7c05fb99bdbb6'
AUDIT_SHA256='330d2fc5f22bffb30f3205f65f4c3d53b38bdb391d7d6d581c96d0afd4165fa8'
MODULE='BusyBeaver.ZFC.ArithmeticHistoryRecurrence254'
PREFIX='SetTheory.BusyBeaver.ZFC.ArithmeticHistoryRecurrence254.'
PROBES=('history_lookup_le','history_lookup','quotient_le','tail_le','minor_le','major_le','value_succ_step','value_succ','mp_parent_gate','mp_parent_children','gen_parent_child')
ARITH={'ArithmeticCantor','ArithmeticCode254','ArithmeticTemplates254','ArithmeticRow254','ArithmeticHistory254'}
def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--repo',type=Path);p.add_argument('--dependency-root',type=Path,required=True)
 p.add_argument('--history-evidence',type=Path,required=True)
 p.add_argument('--core-evidence',type=Path,required=True)
 p.add_argument('--history-cache',type=Path,help='relocated exact five-arithmetic object cache')
 p.add_argument('--core-cache',type=Path,help='relocated source/object-matched core cache')
 p.add_argument('--library-path',type=Path,action='append',default=[])
 p.add_argument('--source',type=Path,help='explicit reviewed source override')
 p.add_argument('--audit',type=Path,help='explicit audit override; exact11/12 contract required')
 p.add_argument('--lean',type=Path,help='real absolute pinned4.32 compiler, not an elan shim')
 p.add_argument('--output',type=Path);p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
 if not __debug__:p.error('Keep assertions enabled; do not use Python -O.')
 repo=a.repo.resolve() if a.repo else next((q for q in Path(__file__).resolve().parents if(q/'.git').exists()),None)
 if repo is None:p.error('Pass --repo outside a checkout.')
 root=a.dependency_root.resolve();source=a.source.resolve() if a.source else repo/SOURCE;audit=a.audit.resolve() if a.audit else repo/AUDIT
 if a.lean:lean=a.lean.resolve()
 else:lean=(Path(os.environ.get('ELAN_HOME',str(Path.home()/'.elan')))/'toolchains/leanprover--lean4---v4.32.0/bin'/('lean.exe' if os.name=='nt' else 'lean')).resolve()
 helper=repo/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py'
 spec=importlib.util.spec_from_file_location('recurrence_cantor_helpers',helper);b=importlib.util.module_from_spec(spec);spec.loader.exec_module(b)
 def dig(q):return b.digest(Path(q))
 work=a.output.resolve() if a.output else Path(tempfile.mkdtemp(prefix='zfc-history-recurrence-check-'))
 b.fail(not work.is_relative_to(repo) and not work.is_relative_to(root),'Use external scratch.')
 b.fail(not work.exists() or not any(work.iterdir()),'Use new/empty scratch.')
 work.mkdir(parents=True,exist_ok=True)
 d=dict(status='PREPARING',scope='Only new internal history recurrence module/audit freshly checked. Five arithmetic modules,12core modules and pinned built external providers explicitly reused; no compiler or execution endpoint.',scratch=str(work),commands=[],dependency_rebuild=False,downloads=False)
 def save():(work/'verification.json').write_text(json.dumps(d,indent=2)+'\n')
 try:
  he=a.history_evidence.resolve();ce=a.core_evidence.resolve();hist=json.loads(he.read_text());core=json.loads(ce.read_text())
  b.fail(hist.get('status')=='PASS' and hist.get('total_named_axiom_probes')==151 and hist.get('total_callers')==164 and hist.get('only_standard_axioms') is True,'Expected successful exact five-arithmetic history evidence.')
  b.fail(hist.get('all_source_and_reused_object_identities_unchanged_after_check') is True and set(hist['fresh_modules'])=={'BusyBeaver.ZFC.'+n for n in ARITH},'Missing prior history closure/post-check.')
  b.fail(str(core.get('status','')).startswith('PASS') and core.get('units',0)>=169 and core.get('all_source_identities_unchanged_after_check') is True and core.get('all_object_identities_unchanged_after_check') is True,'Need successful169+ source/object core integration.')
  b.fail(core.get('audit',{}).get('exit_code')==0 and bool(core.get('fresh_checks')) and all(q.get('exit_code')==0 for q in core['fresh_checks']),'Core fresh checks/audit were not successful.')
  b.fail(lean.is_absolute() and lean.is_file() and lean.name.lower() not in {'elan','elan.exe'},'Use the real absolute pinned compiler.')
  b.fail(dig(lean)==core['compiler']['sha256']==hist['compiler_binary_sha256'],'Actual compiler differs from source-verified baseline.')
  b.fail(a.source is not None or dig(source)==SOURCE_SHA256,'Maintained source changed; review/pass explicit --source.')
  b.fail(a.audit is not None or dig(audit)==AUDIT_SHA256,'Maintained audit changed; review/pass explicit --audit.')
  b.fail(b.lean_imports(source.read_text())==['BusyBeaver.ZFC.ArithmeticHistory254'],'Unexpected new source imports.')
  b.fail(b.lean_imports(audit.read_text())==[MODULE],'Unexpected audit imports.')
  b.fail(re.findall(r'^#print axioms (.+)$',audit.read_text(),re.M)==[PREFIX+n for n in PROBES] and len(re.findall(r'^example\b',audit.read_text(),re.M))==12,'Review changed audit contract.')
  rows={q['module']:q for q in core['source_closure']};reused=[]
  b.fail(len(rows)==len(core['source_closure']),'Duplicate core modules.')
  corecache=a.core_cache.resolve() if a.core_cache else Path(core['cache']).resolve()
  b.fail(corecache.is_dir(),'Core cache unavailable; pass --core-cache.')
  for q in hist['reused_core']:
   c=rows[q['module']];b.fail(q['source_sha256']==c['sha256'] and q['olean_sha256']==c['olean_sha256'],'Old history/core identity mismatch: '+q['module'])
   rel=Path(q['path']);b.fail(not rel.is_absolute() and '..' not in rel.parts and rel.suffix=='.lean','Unsafe core source path.')
   b.fail(c['path']==q['path'],'History/core source path mismatch.')
   s=repo/rel;obj=corecache/Path(q['module'].replace('.','/')).with_suffix('.olean');b.fail(dig(s)==q['source_sha256'] and dig(obj)==q['olean_sha256'],'Changed reused core: '+q['module'])
   reused.append(dict(module=q['module'],source=str(s),source_sha256=q['source_sha256'],object=str(obj.resolve()),object_sha256=q['olean_sha256'],kind='core object matches169evidence'))
  b.fail(len(reused)==12,'Expected12 exact reused core modules.')
  found={}
  def walk(x):
   if isinstance(x,dict):
    s=x.get('source');obj=x.get('module_object',x.get('object'))
    if isinstance(s,dict) and isinstance(obj,dict) and 'path'in s and 'path'in obj and Path(s['path']).stem in ARITH:
     name=Path(s['path']).stem;b.fail(name not in found or found[name]==(s,obj),'Conflicting arithmetic record.');found[name]=(s,obj)
    for v in x.values():walk(v)
   elif isinstance(x,list):
    for v in x:walk(v)
  walk(hist);b.fail(set(found)==ARITH,'Incomplete five-arithmetic object record.')
  arithcache=a.history_cache.resolve() if a.history_cache else Path(hist['module_object']['path']).parents[2]
  b.fail(arithcache.is_dir(),'Arithmetic cache unavailable; pass --history-cache.')
  for name,(s,obj) in found.items():
   actual=repo/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'/(name+'.lean')
   actualobj=arithcache/'BusyBeaver/ZFC'/(name+'.olean')
   b.fail(dig(actual)==s['sha256'] and dig(actualobj)==obj['sha256'],'Changed reused arithmetic module: '+name)
   reused.append(dict(module='BusyBeaver.ZFC.'+name,source=str(actual),source_sha256=s['sha256'],object=str(actualobj.resolve()),object_sha256=obj['sha256'],kind='exact previously fresh five-arithmetic evidence'))
  libs,deps=b.dependency_libraries(root,a.library_path)
  for key in ('Foundation','Mathlib'):
   b.fail(deps[key]['pin']==hist['dependencies'][key]['pin'],'Dependency pin differs from history evidence: '+key)
  b.fail(deps['lake_manifest_sha256']==hist['dependencies']['lake_manifest_sha256'],'Dependency manifest differs from history evidence.')
  for name,q in deps['providers'].items():
   old=hist['dependencies']['providers'].get(name)
   b.fail(old is not None and q['sha256']==old['sha256'],'Actual first dependency provider differs from history evidence: '+name)
  oldproviders={q['module']:q for q in hist['iteration_providers']};providers=[]
  for name in ('Foundation.FirstOrder.Arithmetic.HFS.PRF','Foundation.FirstOrder.Arithmetic.HFS.Seq'):
   b.fail(name in oldproviders,'Missing recorded PRF/Seq provider: '+name)
   rel=Path(name.replace('.','/'));obj=next((q/rel.with_suffix('.olean') for q in libs if(q/rel.with_suffix('.olean')).is_file()),None)
   src=Path(deps['Foundation']['path'])/rel.with_suffix('.lean');old=oldproviders[name]
   b.fail(obj is not None and src.is_file() and dig(obj)==old['object_sha256'] and dig(src)==old['source_sha256'],'Actual first PRF/Seq provider differs from checked history: '+name)
   providers.append(dict(module=name,source=str(src),source_sha256=dig(src),object=str(obj.resolve()),object_sha256=dig(obj),first_provider_in_actual_libraries=True,prior_object=old['object']))
  known={q['module'] for q in reused};external=set()
  for q in reused:
   for imp in b.lean_imports(Path(q['source']).read_text()):
    if imp not in known and not(imp in {'Init','Std','Lean'} or imp.startswith(('Init.','Std.','Lean.'))):external.add(imp)
  b.fail(external=={'Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Tactic.Ring','Foundation.FirstOrder.Arithmetic.HFS.PRF'},'Unexpected reused project import closure.')
  cache=work/'cache';cache.mkdir()
  for q in reused:
   target=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(q['object'])
  inputs=[Path(__file__).resolve(),helper,source,audit,he,ce,lean,root/'lake-manifest.json']
  inputs += [Path(q[k]) for q in reused for k in ('source','object')]
  inputs += [Path(q[k]) for q in providers for k in ('source','object')]
  inputs += [Path(q['path']) for q in deps['providers'].values()]
  for name in deps['providers']:
   parent=Path(deps['Foundation']['path']) if name.startswith('Foundation.') else Path(deps['Mathlib']['path'])
   inputs.append(parent/Path(name.replace('.','/')).with_suffix('.lean'))
  inputs=list(dict.fromkeys(q.resolve() for q in inputs));before={str(q):dig(q) for q in inputs}
  snap=work/'sources'/Path(MODULE.replace('.','/')).with_suffix('.lean');snap.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,snap)
  asnap=work/'Audit.lean';shutil.copyfile(audit,asnap)
  d.update(status='PREPARED_NOT_BUILT' if a.prepare_only else 'RUNNING',source=dict(path=str(source),sha256=dig(source),snapshot=str(snap),explicit_override=a.source is not None),audit_source=dict(path=str(audit),sha256=dig(audit),snapshot=str(asnap),explicit_override=a.audit is not None),history_evidence=dict(path=str(he),sha256=dig(he)),core_evidence=dict(path=str(ce),sha256=dig(ce),units=core['units']),reused_modules=reused,reused_core_count=12,reused_arithmetic_count=5,compiler=dict(path=str(lean),sha256=dig(lean),version=core['compiler']['version']),dependencies=deps,iteration_providers=providers,all_actual_first_providers_match_prior_history=True,provider_cache_scope='Pinned prebuilt dependency caches reused; no whole-cache rebuild or independent attestation.',runner=dict(path=str(Path(__file__).resolve()),sha256=dig(__file__)),before=before,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])));save()
  if a.prepare_only:
   b.fail(before=={str(q):dig(q) for q in inputs},'Input changed during preparation.');print(work/'verification.json');return
  actualversion=subprocess.check_output([str(lean),'--version'],text=True).strip();b.fail(actualversion==d['compiler']['version'],'Compiler version mismatch.')
  env=dict(os.environ,LEAN_PATH=d['LEAN_PATH'],LEAN_NUM_THREADS='1')
  def run(label,cmd):
   start=time.monotonic();r=subprocess.run(cmd,cwd=work,env=env,capture_output=True,text=True);out=r.stdout+r.stderr;(work/(label+'.log')).write_text(out)
   d['commands'].append(dict(label=label,command=cmd,cwd=str(work),exit_code=r.returncode,seconds=round(time.monotonic()-start,6),output=out));save()
   b.fail(r.returncode==0 and 'sorryAx'not in out and "declaration uses 'sorry'"not in out,label+' failed.');print(label,r.returncode,d['commands'][-1]['seconds'],flush=True);return out
  obj=cache/Path(MODULE.replace('.','/')).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
  run('source',[str(lean),'--root='+str(work/'sources'),'-o',str(obj),str(snap)]);objhash=dig(obj)
  d['object_immediately_after_source']=dict(path=str(obj),sha256=objhash);save()
  out=run('audit',[str(lean),str(asnap)])
  reports=[]
  for n,block in re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)",out,re.S):
   ax=[x.strip() for x in block.split(',') if x.strip()];b.fail(set(ax)<=b.STANDARD_AXIOMS,'Unexpected axioms.');reports.append(dict(theorem=n,axioms=ax))
  b.fail([q['theorem'] for q in reports]==[PREFIX+n for n in PROBES],'Unexpected/missing/duplicate axiom probes.')
  after={str(q):dig(q) for q in inputs};b.fail(before==after,'Input/provider/compiler changed.')
  b.fail(dig(obj)==objhash and dig(snap)==d['source']['sha256'] and dig(asnap)==d['audit_source']['sha256'],'Fresh object/snapshot changed.')
  for q in reused:b.fail(dig(cache/Path(q['module'].replace('.','/')).with_suffix('.olean'))==q['object_sha256'],'Overlay object changed.')
  for key in ('Foundation','Mathlib'):
   q=deps[key];b.fail(b.git(Path(q['path']),'rev-parse','HEAD')==q['pin'] and not b.git(Path(q['path']),'status','--porcelain','--untracked-files=no'),'Dependency pin/clean state changed.')
  d.update(status='PASS',after=after,all_source_object_provider_postchecks=True,module_object=dict(path=str(obj),sha256=objhash),axiom_reports=reports,named_axiom_probes=len(reports),callers=12,only_standard_axioms=True,warnings=sum(q['output'].count('warning:') for q in d['commands']));save();print('EVIDENCE',work,flush=True)
 except Exception as error:
  d.update(status='FAIL',error=str(error));save();raise
if __name__=='__main__':main()

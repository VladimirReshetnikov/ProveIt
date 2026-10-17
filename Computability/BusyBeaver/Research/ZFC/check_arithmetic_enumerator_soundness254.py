"""Guarded fresh scheduler soundness and fixed equivalence check.

Explicit successful preservation and forward-direction records supply the
project provider union. Reuse pinned Foundation/Mathlib objects; no build/fetch.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,time

def main():
 p=argparse.ArgumentParser(description=__doc__)
 for k in ('repo','dependency-root','preservation-evidence','forward-evidence','output'):p.add_argument('--'+k,type=Path,required=True)
 p.add_argument('--prepare-only',action='store_true');p.add_argument('--lean',type=Path)
 for k in ('preservation-cache','forward-cache','soundness-source','soundness-audit','equivalence-source','equivalence-audit'):p.add_argument('--'+k,type=Path)
 p.add_argument('--library-path',type=Path,action='append',default=[])
 a=p.parse_args()
 if not __debug__:p.error('Keep assertions enabled; do not use -O.')
 R=a.repo.resolve();D=a.dependency_root.resolve();W=a.output.resolve();assert not W.is_relative_to(R) and not W.is_relative_to(D) and (not W.exists()or not any(W.iterdir()));W.mkdir(parents=True,exist_ok=True)
 helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';spec=importlib.util.spec_from_file_location('cantor_helpers',helper);H=importlib.util.module_from_spec(spec);spec.loader.exec_module(H)
 sha=lambda q:hashlib.sha256(Path(q).read_bytes()).hexdigest()
 Epaths=[a.preservation_evidence.resolve(),a.forward_evidence.resolve()];records=[json.loads(q.read_text())for q in Epaths]
 for e in records:
  assert e['status']=='PASS'and e['only_standard_axioms']is True and e['all_input_provider_postchecks']is True
 assert records[0]['named_axiom_probes']==12 and records[0]['callers']==15
 assert records[1]['named_axiom_probes']==5 and records[1]['callers']==9
 assert all(e.get('all_fresh_objects_unchanged_after_audit')is True for e in records)
 C,version=H.compiler_path(a.lean)
 assert all(e['compiler']['sha256']==sha(C) and e['compiler']['version']==version for e in records)
 libs,deps=H.dependency_libraries(D,a.library_path)
 for e in records:
  for name in ('Foundation','Mathlib'):assert deps[name]['pin']==e['dependencies'][name]['pin'] and deps[name]['tracked_clean'] is True and e['dependencies'][name]['tracked_clean']is True
  assert deps['lake_manifest_sha256']==e['dependencies']['lake_manifest_sha256']
  assert set(deps['providers'])==set(e['dependencies']['providers'])
  for name,q in deps['providers'].items():assert q['sha256']==e['dependencies']['providers'][name]['sha256']
 mods={};alts=[]
 def add(q,relocated=None):
  q=dict(q);m=q['module'];rel=Path(m.replace('.','/')).with_suffix('.lean')
  if m=='FirstOrder.Fol':q['source']=str(R/'Logic/FirstOrder/Lean'/rel)
  else:assert m.startswith('BusyBeaver.ZFC.');q['source']=str(R/'Computability/BusyBeaver/Lean'/rel)
  if relocated:q['object']=str(relocated.resolve()/rel.with_suffix('.olean'))
  assert sha(q['source'])==q['source_sha256']and sha(q['object'])==q['object_sha256']
  if m in mods:
   assert mods[m]['source_sha256']==q['source_sha256']
   if mods[m]['object_sha256']!=q['object_sha256']:
    assert m=='BusyBeaver.ZFC.ArithmeticCantor';q['used_as_provider']=False;alts.append(q)
  else:mods[m]=q
 for e,relocated,expected_module in zip(records,[a.preservation_cache,a.forward_cache],['BusyBeaver.ZFC.ArithmeticCommandPreservation254','BusyBeaver.ZFC.ArithmeticEnumeratorRefutation254']):
  for q in e['reused_modules']:add(q,relocated)
  assert len(e['fresh_modules'])==1
  fresh=e['fresh_modules'][0]
  assert fresh['module']==expected_module and fresh['source_sha256']==e['source']['sha256']
  add(dict(module=fresh['module'],source=e['source']['path'],source_sha256=e['source']['sha256'],object=fresh['path'],object_sha256=fresh['sha256']),relocated)
 assert len(mods)==46 and 'BusyBeaver.ZFC.ArithmeticCommandPreservation254'in mods and 'BusyBeaver.ZFC.ArithmeticEnumeratorRefutation254'in mods
 expected={'Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Tactic.Ring','Foundation.FirstOrder.Arithmetic.HFS.PRF','Foundation.FirstOrder.Arithmetic.HFS.Seq'}
 providers=[]
 assert all({q['module']for q in e['providers']}==expected for e in records)
 for name in sorted(expected):
  rel=Path(name.replace('.','/'));obj=next((x/rel.with_suffix('.olean')for x in libs if(x/rel.with_suffix('.olean')).is_file()),None);dep='Foundation'if name.startswith('Foundation.')else'Mathlib';src=Path(deps[dep]['path'])/rel.with_suffix('.lean');assert obj and src.is_file()
  q=dict(module=name,source=str(src),source_sha256=sha(src),object=str(obj.resolve()),object_sha256=sha(obj),actual_first_provider=True)
  for e in records:
   old=next(q for q in e['providers']if q['module']==name);assert old['source_sha256']==q['source_sha256']and old['object_sha256']==q['object_sha256']
  providers.append(q)
 prefix='SetTheory.BusyBeaver.ZFC.'
 source_root=R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC';audit_root=R/'Computability/BusyBeaver/Research/ZFC'
 items=[dict(short='ArithmeticEnumeratorSoundness254',audit=a.soundness_audit.resolve()if a.soundness_audit else audit_root/'arithmetic_enumerator_soundness254_audit.lean',names=['soundConfig_definable','sound_zero_iff','sound_live','sound_advance','sound_step','sound_run','accepted_of_run_zero','accepted_of_certified_run_zero','accepted_of_zero_work_run_zero'],callers=10),dict(short='ArithmeticEnumeratorEquivalence254',audit=a.equivalence_audit.resolve()if a.equivalence_audit else audit_root/'arithmetic_enumerator_equivalence254_audit.lean',names=['blank_live','accepted_iff_blank_halts','equivalenceSentence_true','isigma1_proves_equivalence','peano_proves_equivalence'],callers=7)]
 for x in items:
  x['module']='BusyBeaver.ZFC.'+x['short'];override=a.soundness_source if x['short']=='ArithmeticEnumeratorSoundness254'else a.equivalence_source;x['source']=override.resolve()if override else source_root/(x['short']+'.lean');x['qualified_names']=[prefix+x['short']+'.'+n for n in x['names']]
  source_hashes={'ArithmeticEnumeratorSoundness254':'d3ce1352d7531e7ae7a6e7a9edd2f5f591a06b0367e8e143b78232aafbc1330f','ArithmeticEnumeratorEquivalence254':'7fcc5c383243a027c2a67d0a3a510ce4a82c5b183dc54408c95569b596214dc0'}
  audit_hashes={'ArithmeticEnumeratorSoundness254':'a2ce09ad633c0d3b0ffa243e0997a487543a581fcda946b0840453a4666d6634','ArithmeticEnumeratorEquivalence254':'69d27b72c79148535c64c2f47a98e521578172cec93e685bc239e3685114f819'}
  assert override is not None or sha(x['source'])==source_hashes[x['short']]
  audit_override=a.soundness_audit if x['short']=='ArithmeticEnumeratorSoundness254'else a.equivalence_audit
  assert audit_override is not None or sha(x['audit'])==audit_hashes[x['short']]
  expected_imports={'ArithmeticEnumeratorSoundness254':['BusyBeaver.ZFC.ArithmeticCommandPreservation254','BusyBeaver.ZFC.ArithmeticEnumeratorRun254'],'ArithmeticEnumeratorEquivalence254':['BusyBeaver.ZFC.ArithmeticEnumeratorSoundness254','BusyBeaver.ZFC.ArithmeticEnumeratorRefutation254']}
  assert H.lean_imports(x['source'].read_text())==expected_imports[x['short']]
  assert H.lean_imports(x['audit'].read_text())==[x['module']]
  assert re.findall(r'^#print axioms (\S+)$',x['audit'].read_text(),re.M)==x['qualified_names']
  assert len(re.findall(r'^example\b',x['audit'].read_text(),re.M))==x['callers']
 localmod={x['module']:x for x in items};required={};external=set();visiting=set()
 def visit(m):
  if m in required:return
  assert m not in visiting and m in mods;visiting.add(m);q=mods[m]
  for n in H.lean_imports(Path(q['source']).read_text()):
   if n in mods:visit(n)
   else:assert n.startswith(('Foundation.','Mathlib.'));external.add(n)
  visiting.remove(m);required[m]=q
 for x in items:
  for m in H.lean_imports(x['source'].read_text()):
   if m not in localmod:visit(m)
 assert set(required)==set(mods),'Extra/missing project provider.'
 cache=W/'cache';cache.mkdir();snap=W/'sources';(snap/'BusyBeaver/ZFC').mkdir(parents=True)
 for q in mods.values():
  dest=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(Path(q['object']).resolve())
 actual=[]
 for q in mods.values():
  rel=Path(q['module'].replace('.','/')).with_suffix('.olean');first=next((x/rel for x in [cache,*libs]if(x/rel).is_file()),None);assert first and sha(first)==q['object_sha256'];actual.append(dict(module=q['module'],actual_first=str(first),resolved=str(first.resolve()),sha256=sha(first)))
 direct=[]
 for m in sorted(external):
  rel=Path(m.replace('.','/'));obj=next((x/rel.with_suffix('.olean')for x in libs if(x/rel.with_suffix('.olean')).is_file()),None);dep='Foundation'if m.startswith('Foundation.')else'Mathlib';src=Path(deps[dep]['path'])/rel.with_suffix('.lean');assert obj and src.is_file();direct.append(dict(module=m,source=str(src),source_sha256=sha(src),object=str(obj.resolve()),object_sha256=sha(obj),actual_first_provider=True))
 for x in items:
  x['snapshot']=snap/'BusyBeaver/ZFC'/(x['short']+'.lean');x['audit_snapshot']=snap/(x['short']+'Audit.lean');shutil.copyfile(x['source'],x['snapshot']);shutil.copyfile(x['audit'],x['audit_snapshot'])
 inputs=[Path(__file__).resolve(),helper,C,*Epaths,D/'lake-manifest.json']
 for x in items:inputs.extend(x[k]for k in ('source','audit','snapshot','audit_snapshot'))
 for q in list(mods.values())+alts+providers+direct:inputs.extend([Path(q['source']),Path(q['object'])])
 inputs.extend(Path(q['path'])for q in deps['providers'].values());inputs=list(dict.fromkeys(q.resolve()for q in inputs));before={str(q):sha(q)for q in inputs}
 env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
 d=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope=__doc__,prepare_only=a.prepare_only,compiler=dict(path=str(C),version=version,sha256=sha(C)),evidence=[dict(path=str(p),sha256=sha(p))for p in Epaths],reused_count=len(mods),reused_modules=list(mods.values()),same_source_object_alternatives=alts,providers=providers,actual_project_providers=actual,direct_external_providers=direct,exact_project_import_closure=True,dependencies=deps,commands=[],before=before,LEAN_PATH=env['LEAN_PATH'],dependency_build=False,downloads=False,new_modules=[dict(module=x['module'],source=dict(path=str(x['source']),sha256=sha(x['source']),snapshot=str(x['snapshot'])),audit=dict(path=str(x['audit']),sha256=sha(x['audit']),snapshot=str(x['audit_snapshot'])),named_axiom_probes=len(x['names']),callers=x['callers'])for x in items])
 def save():(W/'verification.json').write_text(json.dumps(d,indent=2)+'\n')
 def post():
  after={str(q):sha(q)for q in inputs};assert before==after
  for q in mods.values():assert sha(cache/Path(q['module'].replace('.','/')).with_suffix('.olean'))==q['object_sha256']
  _,depafter=H.dependency_libraries(D,a.library_path);assert deps==depafter
  d.update(after=after,all_input_provider_postchecks=True)
 save()
 if a.prepare_only:post();save();print(W/'verification.json');return
 fresh=[]
 def run(label,source,obj=None):
  cmd=[str(C),'-M4096','--root='+str(snap)]+(['-o',str(obj)]if obj else[])+[str(source)];t=time.monotonic();r=subprocess.run(cmd,cwd=snap,env=env,text=True,capture_output=True);o=r.stdout+r.stderr;(W/(label+'.log')).write_text(o);d['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-t,exit_code=r.returncode,output=o));save();assert r.returncode==0 and'sorryAx'not in o and"declaration uses 'sorry'"not in o,o;print(label,'PASS',round(time.monotonic()-t,3),flush=True);return o
 try:
  for x in items:
   obj=cache/Path(x['module'].replace('.','/')).with_suffix('.olean');run(x['short']+'Source',x['snapshot'],obj);oh=sha(obj);fresh.append(dict(module=x['module'],path=str(obj),sha256=oh,source_sha256=sha(x['source'])));out=run(x['short']+'Audit',x['audit_snapshot']);reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S);assert[n for n,_ in reports]==x['qualified_names'];assert all(set(v.strip()for v in vs.split(',')if v.strip())<={'propext','Classical.choice','Quot.sound'}for _,vs in reports)
   for q in fresh:assert sha(q['path'])==q['sha256']
  post();d.update(status='PASS',fresh_modules=fresh,all_fresh_objects_unchanged_after_audit=True,named_axiom_probes=sum(len(x['names'])for x in items),callers=sum(x['callers']for x in items),only_standard_axioms=True,warnings=sum(q['output'].count('warning:')for q in d['commands']))
 except Exception as ex:d.update(status='FAIL',error=str(ex));save();raise
 save();print(W/'verification.json')

if __name__=='__main__':main()

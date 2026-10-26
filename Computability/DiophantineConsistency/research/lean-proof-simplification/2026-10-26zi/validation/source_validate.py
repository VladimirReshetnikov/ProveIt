#!/usr/bin/env python3
"""Offline identity/patch/generator checks; never runs Lean or installs anything."""
import argparse,hashlib,json,re,shutil,subprocess,tempfile
from pathlib import Path
from plan_tools import inspect_plan,PIN
from static_audit import mask_noncode,PATTERNS
OLD='22e020937caa81d0cb72a4f63071d6c0bcc1eba9'
PREFIX='Computability/DiophantineConsistency/Lean/DiophantineConsistency/'
MATHLIB='81a5d257c8e410db227a6665ed08f64fea08e997'
PATCHES=['helical/patches/H1.patch','helical/patches/H2.patch',
 'bridges/patches/WangTiles942FinishConstruction.lean.patch','bridges/patches/WangTiles942TraceCycle.lean.patch']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def blob(data):return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
def manifests(root):
 results=[]
 for name,folder,pin in [('source_manifest.json','sources',PIN),('dependency_manifest.json','dependencies',PIN),('comparison_manifest.json','comparison_sources',OLD)]:
  m=json.loads((root/'provenance'/name).read_text());errors=[];seen=set();base=(root/folder).resolve()
  if m['commit']!=pin:errors.append('Wrong commit')
  if not m['sources']:errors.append('Empty manifest')
  for entry in m['sources']:
   path=entry['path'];p=(base/path).resolve()
   if path in seen:errors.append(path+': duplicate')
   seen.add(path)
   if not p.is_relative_to(base) or not p.is_file():errors.append(path+': absent or unsafe');continue
   raw=p.read_bytes()
   if blob(raw)!=entry['sha'] or sha(p)!=entry['sha256']:errors.append(path+': hash mismatch')
  results.append(dict(manifest=name,root=folder,count=len(seen),errors=errors))
 return results

def declarations(raw):
 code=mask_noncode(raw)
 starts=list(re.finditer(r'^(?:(private|noncomputable|protected) )?(theorem|lemma|def|abbrev|structure|inductive)\s+([^\s:(]+)',code,re.M));result={}
 for i,m in enumerate(starts):
  end=starts[i+1].start() if i+1<len(starts) else code.find('\nend ',m.start())
  if end<0:end=len(code)
  part=code[m.start():end]
  if m[2] in ('theorem','lemma'):part=part.split(':=',1)[0]
  result[m[3]]=(m[1],m[2],' '.join(part.split()))
 return result

def validate(root):
 errors=[];before=manifests(root);errors += [e for r in before for e in r['errors']]
 counts={r['root']:r['count'] for r in before};counts['active_Lean']=len(list((root/'sources/Computability/DiophantineConsistency/Lean').rglob('*.lean')))
 if counts!={'sources':914,'dependencies':6,'comparison_sources':11,'active_Lean':637}:errors.append('Unexpected corpus counts')
 snapshot=subprocess.run(['python3',str(root/'provenance/verify_snapshot.py')],text=True,capture_output=True)
 if snapshot.returncode:errors.append('Active source/tree delta verification failed')
 plan=inspect_plan(json.loads((root/'validation/replay_plan.json').read_text()),root);errors+=plan['errors']
 # No baseline import may reach an edited overlay through an omitted connector.
 graph={}
 active_root=root/'sources/Computability/DiophantineConsistency/Lean'
 for path in active_root.rglob('*.lean'):
  name=str(path.relative_to(active_root).with_suffix('')).replace('/','.')
  graph[name]=[t for line in re.findall(r'^import\s+([^\n]+)',mask_noncode(path.read_text()),re.M) for t in line.split()]
 overlay={p['module'] for p in plan['probes']};external={n for p in plan['probes'] for n in p['imports']}-overlay
 stale_paths=[]
 def visit(name,path):
  if name in overlay:stale_paths.append(path+[name]);return
  if name in path:return
  for dep in graph.get(name,[]):visit(dep,path+[name])
 for name in sorted(external):visit(name,[])
 if stale_paths:errors.append('Unrebuilt connector paths to overlay: '+repr(stale_paths))
 audit=[]
 for p in json.loads((root/'validation/replay_plan.json').read_text())['probes']:
  origin=root/p['origin']; raw=origin.read_text(); actual=(root/p['source']).read_text()
  expected=raw+'\n-- UNEXECUTED audit commands, excluded from every candidate size metric.\n'+'\n'.join('#print axioms '+n for n in p['expected'])+'\n'
  ok=actual==expected and sha(origin)==p['origin_sha256']
  if not ok:errors.append(p['source']+': audit prefix/origin mismatch')
  audit.append(dict(source=p['source'],origin=p['origin'],public_audit_count=len(p['expected']),exact_origin_prefix_and_suffix=ok,sha256=sha(root/p['source'])))
 library=root/'helical/dependencies/Periodic.lean';metadata=json.loads((root/'helical/dependencies/Periodic.source.json').read_text())
 library_ok=metadata['ref']==MATHLIB and metadata['sha']==blob(library.read_bytes())
 lock=json.loads((root/'sources/lake-manifest.json').read_text())
 library_ok &= any(p.get('name')=='mathlib' and p.get('rev')==MATHLIB for p in lock['packages'])
 if not library_ok:errors.append('Pinned library evidence mismatch')
 license_file=root/'helical/dependencies/LICENSE.mathlib';license_meta=json.loads((root/'helical/dependencies/LICENSE.source.json').read_text())
 license_ok=(license_meta['commit']==MATHLIB and license_meta['git_blob']==blob(license_file.read_bytes()) and license_meta['sha256']==sha(license_file) and license_meta['bytes']==license_file.stat().st_size)
 if not license_ok:errors.append('Pinned Mathlib license identity mismatch')
 patches=[];contracts=[];reproduction=[]
 with tempfile.TemporaryDirectory(prefix='round4-source-validation-') as td:
  tmp=Path(td);copy=tmp/'source';shutil.copytree(root/'sources',copy)
  for relative in PATCHES:
   p=root/relative;headers=re.findall(r'^\+\+\+ b/(.*)$',p.read_text(),re.M)
   if not headers or any(Path(n).is_absolute() or '..' in Path(n).parts for n in headers):errors.append(relative+': unsafe patch');continue
   check=subprocess.run(['git','apply','--check','--',str(p)],cwd=copy,text=True,capture_output=True)
   applied=subprocess.run(['git','apply','--',str(p)],cwd=copy,text=True,capture_output=True) if not check.returncode else None
   result=dict(path=relative,sha256=sha(p),check_exit=check.returncode,apply_exit=applied.returncode if applied else None,targets=[])
   if check.returncode or applied.returncode:errors.append(relative+': patch failed')
   else:
    for target in headers:
     name=Path(target).name;proposed=root/('helical/proposed' if relative.startswith('helical') else 'bridges/candidate')/name
     ok=(copy/target).read_bytes()==proposed.read_bytes()
     if not ok:errors.append(target+': patch differs from full module')
     result['targets'].append(dict(path=target,proposed=str(proposed.relative_to(root)),sha256=sha(proposed),identical=ok))
     old=(root/'sources'/target).read_text();new=proposed.read_text();a,b=declarations(old),declarations(new)
     changed=[n for n,v in a.items() if b.get(n)!=v]
     if changed:errors.append(target+': existing statements/definitions changed: '+repr(changed))
     if re.findall(r'^import[^\n]*',old,re.M)!=re.findall(r'^import[^\n]*',new,re.M):errors.append(target+': imports changed')
     forbidden=[n for n,patt in PATTERNS.items() if re.search(patt,mask_noncode(new))]
     if forbidden:errors.append(target+': lexical exclusions '+repr(forbidden))
     contracts.append(dict(file=target,old_declarations_preserved=len(a),new_declarations=sorted(b.keys()-a.keys()),changed=changed,forbidden_tokens=forbidden,original_lines=len(old.splitlines()),proposed_lines=len(new.splitlines())))
   patches.append(result)
  regen=tmp/'regenerate';shutil.copytree(root/'sources',regen/'sources')
  for folder in ['helical','bridges','validation']:shutil.copytree(root/folder,regen/folder,ignore=shutil.ignore_patterns('__pycache__'))
  generated=[n for n in ['helical/build_proposals.py','bridges/build_candidates.py','validation/build_replay_plan.py']]
  for script in generated:
   run=subprocess.run(['python3',str(regen/script)],cwd=regen,text=True,capture_output=True)
   if run.returncode:errors.append(script+': reproduction execution failed')
   reproduction.append(dict(generator=script,exit=run.returncode,stderr=run.stderr))
  outputs=['helical/metrics.json','bridges/validation/metrics.json','validation/replay_plan.json']+PATCHES
  outputs += [p['origin'] for p in json.loads((root/'validation/replay_plan.json').read_text())['probes'] if p['role']=='changed_candidate']
  outputs += [p['source'] for p in json.loads((root/'validation/replay_plan.json').read_text())['probes']]
  matches={name:(root/name).read_bytes()==(regen/name).read_bytes() for name in outputs}
  errors += [name+': nonreproducible' for name,ok in matches.items() if not ok]
 after=manifests(root);errors += [e for r in after for e in r['errors']]
 return dict(status='PASS_SOURCE_ONLY_UNCOMPILED' if not errors else 'FAIL',pin=PIN,counts=counts,
  source_hashes_before=before,source_hashes_after=after,snapshot_replay=json.loads(snapshot.stdout) if snapshot.returncode==0 else snapshot.stderr,
  plan=plan,overlay_closure=dict(baseline_direct_imports=sorted(external),stale_connector_paths=stale_paths),audit_sources=audit,library_evidence=dict(pin=MATHLIB,blob_sha1=blob(library.read_bytes()),sha256=sha(library),passed=library_ok,license_sha256=sha(license_file),license_passed=license_ok),
  patches=patches,contracts=contracts,generator_runs=reproduction,generator_outputs_identical=matches,errors=errors,
  lean_executions=0,installations=0,not_established=['Lean elaboration','kernel checking','actual axiom outputs','composite assumed-applied baseline build','project integration','runtime performance'])
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--bundle',type=Path,default=Path(__file__).resolve().parents[1]);ap.add_argument('--json',type=Path);a=ap.parse_args();r=validate(a.bundle.resolve());s=json.dumps(r,indent=2)+'\n'
 if a.json:a.json.write_text(s)
 print(s);raise SystemExit(bool(r['errors']))

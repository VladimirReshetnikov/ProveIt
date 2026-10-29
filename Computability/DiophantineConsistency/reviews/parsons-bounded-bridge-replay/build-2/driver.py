from pathlib import Path
import os,subprocess,tempfile,json,hashlib,shutil,time,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
S=R/'Computability/DiophantineConsistency/Lean'
SRC=S/'DiophantineConsistency'
provider=Path('/tmp/pra-bounded-induction-independent-rm8rcvo8/lib')
providerManifest=R/'Computability/DiophantineConsistency/reviews/pra-bounded-induction-author-replay/manifest.json'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
manifestBytes=providerManifest.read_bytes(); manifest=json.loads(manifestBytes)
for n,row in manifest['parent_modules'].items():
 src=SRC/(n+'.lean');obj=provider/'DiophantineConsistency'/(n+'.olean')
 assert src.is_file() and sha(src)==row['source_sha256'],f'candidate source changed: {n}'
 assert obj.is_file() and sha(obj)==row['object_sha256'],f'candidate object changed: {n}'
for n,row in manifest['modules'].items():
 src=SRC/(n+'.lean');obj=provider/'DiophantineConsistency'/(n+'.olean')
 assert src.is_file() and sha(src)==row['source_sha256'],f'candidate source changed: {n}'
 assert obj.is_file() and sha(obj)==row['object_sha256'],f'candidate object changed: {n}'
ruleSrc=SRC/'ParsonsRule.lean';ruleObj=Path('/tmp/parsons-case-overlay/DiophantineConsistency/ParsonsRule.olean')
assert sha(ruleSrc)=='7fe1dd093fa3ff9585fa37968e0bf75d483b743c9b18fa33c4587a677bb15325'
assert sha(ruleObj)=='eb5c49e2362e7d7f05b6e7dea5d0f671134657c57f0f09a9ec959f7c01a57ec3'
names=['ParsonsHierarchyMap','ParsonsMapInduction','ParsonsBoundedProof','ParsonsBoundedComparison','ParsonsISigmaZeroComparison','ParsonsBoundedComparisonChecks']
P=Path(tempfile.mkdtemp(prefix='parsons-bounded-bridge-build-'));lib=P/'lib';lib.mkdir();dst=lib/'DiophantineConsistency';dst.mkdir();(lib/'Foundation').symlink_to((provider/'Foundation').resolve(),target_is_directory=True)
for root in [provider/'DiophantineConsistency',Path('/tmp/parsons-case-overlay/DiophantineConsistency')]:
 for f in root.glob('*.olean'):
  if f.stem not in names and not (dst/f.name).exists(): (dst/f.name).symlink_to(f.resolve())
shutil.copyfile(__file__,P/'driver.py');(P/'provider-manifest.json').write_bytes(manifestBytes)
base=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],text=True,cwd=R).strip();env=dict(os.environ,LEAN_PATH=str(lib)+':/home/codex/src/Proofs/.lake/build/lib/lean:'+base,LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
def rec(p):
 p=Path(p);b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
for n in names: shutil.copyfile(SRC/(n+'.lean'),P/(n+'.lean'))
records=[]
for n in names:
 src=SRC/(n+'.lean');snap=P/(n+'.lean');assert sha(src)==sha(snap);obj=dst/(n+'.olean');log=P/(n+'.log');timing=P/(n+'.time');cmd=['lean','-M6000','-j1','-DElab.async=false','-R',str(S),'-o',str(obj),str(src)];start=time.monotonic()
 with log.open('w') as f: code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 row={'module':n,'source':rec(src),'snapshot':rec(snap),'command':cmd,'exit_code':code,'seconds':time.monotonic()-start,'log':rec(log),'timing':rec(timing),'object':rec(obj) if obj.exists() else None};records.append(row);(P/'state.json').write_text(json.dumps({'status':'RUNNING','records':records},indent=2)+'\n');print(log.read_text(),flush=True);assert code==0 and not re.search(r'\b(?:error|warning|sorryAx)\b',log.read_text());assert sha(src)==sha(snap)
assert providerManifest.read_bytes()==manifestBytes
for n,row in manifest['parent_modules'].items():
 assert sha(SRC/(n+'.lean'))==row['source_sha256'] and sha(provider/'DiophantineConsistency'/(n+'.olean'))==row['object_sha256']
for n,row in manifest['modules'].items():
 assert sha(SRC/(n+'.lean'))==row['source_sha256'] and sha(provider/'DiophantineConsistency'/(n+'.olean'))==row['object_sha256']
assert sha(ruleSrc)=='7fe1dd093fa3ff9585fa37968e0bf75d483b743c9b18fa33c4587a677bb15325' and sha(ruleObj)=='eb5c49e2362e7d7f05b6e7dea5d0f671134657c57f0f09a9ec959f7c01a57ec3'
(P/'state.json').write_text(json.dumps({'status':'PASS','records':records,'LEAN_PATH':env['LEAN_PATH'],'candidate_provider':str(provider),'provider_manifest_sha256':hashlib.sha256(manifestBytes).hexdigest(),'authenticated_candidate_parent_modules':len(manifest['parent_modules']),'qualification':'Candidate provider source/object chain verified against frozen sibling manifest; ParsonsRule direct source/object verified; earlier Parsons providers and Foundation/package objects inherited.'},indent=2)+'\n');print('PASS',P,flush=True)

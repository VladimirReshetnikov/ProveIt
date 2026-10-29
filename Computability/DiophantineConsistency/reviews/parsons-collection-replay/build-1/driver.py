from pathlib import Path
import os,subprocess,tempfile,json,hashlib,shutil,time,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs');S=R/'Computability/DiophantineConsistency/Lean';P=Path(tempfile.mkdtemp(prefix='parsons-collection-build-'));lib=P/'lib';lib.mkdir(); (lib/'DiophantineConsistency').mkdir(); [(lib/'DiophantineConsistency'/n).symlink_to(Path('/tmp/parsons-case-overlay/DiophantineConsistency')/n) for n in ['ParsonsRule.olean','ParsonsGuard.olean','ParsonsSelection.olean','ParsonsPrenex.olean']]; shutil.copyfile(__file__,P/'driver.py');names=['ParsonsCollection','ParsonsCollectionChecks'];records=[]
base=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],text=True,cwd=R).strip();env=dict(os.environ,LEAN_PATH=str(lib)+':/home/codex/src/Proofs/.lake/build/lib/lean:'+base,LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
def rec(p):
 p=Path(p);b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
for n in names:
 src=S/'DiophantineConsistency'/(n+'.lean');shutil.copyfile(src,P/(n+'.lean'))
for n in names:
 src=S/'DiophantineConsistency'/(n+'.lean');snap=P/(n+'.lean');assert rec(src)['sha256']==rec(snap)['sha256'];output=lib/'DiophantineConsistency'/(n+'.olean');output.parent.mkdir(parents=True,exist_ok=True);log=P/(n+'.log');timing=P/(n+'.time');cmd=['lean','-M6000','-j1','-DElab.async=false','-R',str(S),'-o',str(output),str(src)];start=time.monotonic()
 with log.open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 row={'module':n,'source':rec(src),'snapshot':rec(snap),'command':cmd,'exit_code':code,'seconds':time.monotonic()-start,'log':rec(log),'timing':rec(timing),'object':rec(output) if output.exists() else None};records.append(row);(P/'state.json').write_text(json.dumps({'status':'RUNNING','records':records},indent=2)+'\n');print(log.read_text(),flush=True);assert code==0 and not re.search(r'\b(?:error|warning|sorryAx)\b',log.read_text());assert rec(src)['sha256']==rec(snap)['sha256']
(P/'state.json').write_text(json.dumps({'status':'PASS','records':records,'LEAN_PATH':env['LEAN_PATH'],'qualification':'Foundation and package objects inherited from existing compiled directory; no independent transitive source audit'},indent=2)+'\n');print('PASS',P,flush=True)

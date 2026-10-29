from pathlib import Path
import subprocess,tempfile,os,json,hashlib,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs');S=R/'Computability/DiophantineConsistency/Lean';old=Path('/tmp/parsons-cut-free-build-8l3wqy_4');previous=json.loads((old/'result.json').read_text());Q=Path(tempfile.mkdtemp(prefix='parsons-cut-free-replay-'));lib=Q/'lib';lib.mkdir();shutil.copyfile(__file__,Q/'driver.py');env=dict(os.environ);env['LEAN_PATH']=str(lib)+':'+previous['LEAN_PATH'].split(':',1)[1];rows=[]
for rec in previous['records']:
 src=Path(rec['source']['path']); snap=Q/(rec['module']+'.lean');shutil.copyfile(src,snap);assert hashlib.sha256(snap.read_bytes()).hexdigest()==rec['snapshot']['sha256']
for rec in previous['records']:
 m=rec['module'];src=Path(rec['source']['path']);out=lib/'DiophantineConsistency'/(m+'.olean');out.parent.mkdir(parents=True,exist_ok=True);log=Q/(m+'.log');cmd=['lean','-M6000','-j1','-DElab.async=false','-R',str(S),'-o',str(out),str(src)]
 with log.open('w') as f:code=subprocess.run(cmd,env=env,cwd=R,stdout=f,stderr=subprocess.STDOUT).returncode
 def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
 row={'module':m,'command':cmd,'code':code,'object_sha256':sha(out) if out.exists() else None,'log_sha256':sha(log)};rows.append(row);assert code==0 and row['object_sha256']==rec['object']['sha256'] and row['log_sha256']==rec['log']['sha256'];print(m,'PASS',flush=True)
(Q/'result.json').write_text(json.dumps({'status':'PASS','scope':'Two new modules only; historical Foundation/Mathlib objects as explicit inherited boundary, not fresh closure audit.','records':rows},indent=2)+'\n');print(Q,flush=True)

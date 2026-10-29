from pathlib import Path
import os,subprocess,hashlib,json,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs'); S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency';root=Path('/tmp/pra-universal-equivalence-current');lib=root/'lib';logs=root/'logs';base=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=R,text=True).strip();env=dict(os.environ,LEAN_PATH=str(lib)+':'+base,LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();records=[]
for name in ['PRAUniversalCandidateChecks','PRAUniversalModelLemmasChecks','PRAUniversalInductionChecks','PRAUniversalEquivalenceChecks']:
 src=S/(name+'.lean');snap=logs/(name+'.lean');snap.write_bytes(src.read_bytes()); out=lib/'DiophantineConsistency'/(name+'.olean');cmd=['lean','-M6000','-j1','-DElab.async=false',str(src),'-o',str(out)];start=time.monotonic();p=subprocess.run(cmd,cwd=R,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);(logs/(name+'.log')).write_text(p.stdout);records.append({'name':name,'exit':p.returncode,'source_sha':sha(src),'object_sha':sha(out) if out.exists() else None,'log_sha':sha(logs/(name+'.log')),'seconds':time.monotonic()-start});print(name,p.returncode,p.stdout,flush=True)
 if p.returncode or 'warning:' in p.stdout or 'sorryAx' in p.stdout:raise SystemExit(1)
 assert sha(src)==sha(snap)
(root/'checks-state.json').write_text(json.dumps(records,indent=2))

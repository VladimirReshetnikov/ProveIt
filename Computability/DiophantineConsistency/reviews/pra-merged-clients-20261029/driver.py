from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency';P=Path(tempfile.mkdtemp(prefix='pra-merged-clients-'));lib=P/'lib';dst=lib/'DiophantineConsistency';dst.mkdir(parents=True);logs=P/'logs';logs.mkdir()
parents={'PRAFunctionCodes':'/tmp/pra-function-codes-root-ld2dgh6b','PRAFiniteFunctionCodes':'/tmp/pra-finite-function-codes-root-fjtcwus4','PRACodeEncoding':'/tmp/pra-code-encoding-root-e6ee_nqd','PRALanguage':'/tmp/pra-language-root-ugx71zo4','PRATheory':'/tmp/pra-theory-root-52004dsz'}
for n,p in parents.items():(dst/(n+'.olean')).symlink_to(Path(p)/'lib/DiophantineConsistency'/(n+'.olean'))
(lib/'Foundation').symlink_to('/tmp/current-hierarchy2011-author-betz9tp8/lib/Foundation')
names=['PRAAddOne','PRAAddOneChecks','PRAExhaustion','PRAExhaustionChecks']; sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();pins={n:sha(S/(n+'.lean')) for n in names}
for n in names:shutil.copyfile(S/(n+'.lean'),logs/(n+'.lean'))
paths=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=R,text=True).strip().split(':');env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*[p for p in paths if '/.lake/packages/' in p or '/.elan/toolchains/' in p]]),LEAN_NUM_THREADS='1');rows=[]
for n in names:
 p=S/(n+'.lean');assert sha(p)==pins[n];out=dst/(n+'.olean');log=logs/(n+'.log');cmd=['lean','-M6000','-j1','-DElab.async=false','-o',str(out),str(p)];t=time.monotonic()
 with log.open('w') as f:code=subprocess.run(cmd,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 rows.append(dict(name=n,source=sha(p),exit=code,seconds=time.monotonic()-t,log=sha(log),object=sha(out) if out.exists() else None));(P/'state.json').write_text(json.dumps(dict(status='RUNNING',rows=rows),indent=2));print(n,code,flush=True);assert code==0;assert sha(p)==pins[n]
(P/'state.json').write_text(json.dumps(dict(status='PASS',rows=rows,lean_path=env['LEAN_PATH']),indent=2));print('PASS',P,flush=True)

from pathlib import Path
import os,subprocess,tempfile,hashlib,json,time,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs'); S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'; P=Path(tempfile.mkdtemp(prefix='pra-q-compat-root-')); L=P/'lib/DiophantineConsistency';L.mkdir(parents=True); logs=P/'logs';logs.mkdir()
(L/'PRAFunctionCodes.olean').symlink_to('/tmp/pra-function-codes-root-ld2dgh6b/lib/DiophantineConsistency/PRAFunctionCodes.olean')
(L/'PRAFiniteFunctionCodes.olean').symlink_to('/tmp/pra-finite-function-codes-root-fjtcwus4/lib/DiophantineConsistency/PRAFiniteFunctionCodes.olean')
(L/'PRACodeEncoding.olean').symlink_to('/tmp/pra-code-encoding-root-e6ee_nqd/lib/DiophantineConsistency/PRACodeEncoding.olean')
(P/'lib/Foundation').symlink_to('/tmp/current-hierarchy2011-author-betz9tp8/lib/Foundation')
(L/'PRALanguage.olean').symlink_to('/tmp/pra-language-root-ugx71zo4/lib/DiophantineConsistency/PRALanguage.olean')
(L/'PRATheory.olean').symlink_to('/tmp/pra-q-current-refresh-_iu8xbm0/lib/DiophantineConsistency/PRATheory.olean')
for n in ['PRAAddOne','PRAAddition','PRAMultiplication','PRAExhaustion']:
 (L/(n+'.olean')).symlink_to(Path('/tmp/pra-q-current-refresh-_iu8xbm0/lib/DiophantineConsistency')/(n+'.olean'))
names=['PRAQCompatibility','PRAQCompatibilityChecks']; pins=['bc073db7a31afda50cbe41477c40761a0ed1e70e7924516b88ee21eb07016bc8','6dec58797c35414f9d96cea4707867677e1d48bbfd2a0bf0a77bf247a5e084c3']
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
for name,pin in zip(names,pins):
 p=S/(name+'.lean');assert sha(p)==pin;shutil.copyfile(p,logs/(name+'.lean'))
lakepath=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=R,text=True).strip().split(':');package=[p for p in lakepath if '/.lake/packages/' in p or '/.elan/toolchains/' in p]; env=dict(os.environ,LEAN_PATH=':'.join([str(P/'lib'),'/tmp/pra-function-codes-root-ld2dgh6b/lib',*package]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
rows=[]
for name,pin in zip(names,pins):
 p=S/(name+'.lean');assert sha(p)==pin; assert shutil.disk_usage('/tmp').free>512*1024**2
 cmd=['lean','-M6000','-j1','-DElab.async=false','-o',str(L/(name+'.olean')),str(p)];start=time.monotonic()
 with (logs/(name+'.log')).open('w') as f: code=subprocess.run(cmd,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 row=dict(module=name,exit=code,seconds=time.monotonic()-start,source=sha(p),object=sha(L/(name+'.olean')) if (L/(name+'.olean')).exists() else None,log=sha(logs/(name+'.log')));rows.append(row);(P/'state.json').write_text(json.dumps({'status':'RUNNING','rows':rows},indent=2));print(name,code,flush=True);assert code==0
 expected=Path('/tmp/pra-q-current-refresh-_iu8xbm0/lib/DiophantineConsistency')/(name+'.olean');assert sha(expected)==row['object']
 authorlog=Path('/tmp/pra-q-compat-author-ihfc8jl8/logs')/(name+'.log');assert not authorlog.exists() or sha(authorlog)==row['log'];assert sha(p)==pin
(P/'state.json').write_text(json.dumps({'status':'PASS','rows':rows,'lean_path':env['LEAN_PATH']},indent=2));print('PASS',P,flush=True)

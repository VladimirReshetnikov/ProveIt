from pathlib import Path
import os,subprocess,tempfile,hashlib,json,time,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs'); S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'; P=Path(tempfile.mkdtemp(prefix='pra-finite-function-codes-root-')); L=P/'lib/DiophantineConsistency';L.mkdir(parents=True); logs=P/'logs';logs.mkdir()
(L/'PRAFunctionCodes.olean').symlink_to('/tmp/pra-function-codes-root-ld2dgh6b/lib/DiophantineConsistency/PRAFunctionCodes.olean')
names=['PRAFiniteFunctionCodes','PRAFiniteFunctionCodesChecks']; pins=['f0a5ba7482344477c2c7ca5ec2544f127ede62ec30e60b1101bfaed7be94db74','edb69354ee75b94aeac0a5f43c157174e12c38e5041123b88950fe6e4d953829']
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
 expected=Path('/tmp/pra-function-codes-20261029/lib/DiophantineConsistency')/(name+'.olean');assert sha(expected)==row['object']
 authorlog=Path('/tmp/pra-function-codes-20261029/logs')/(name+'.log');assert not authorlog.exists() or sha(authorlog)==row['log'];assert sha(p)==pin
(P/'state.json').write_text(json.dumps({'status':'PASS','rows':rows,'lean_path':env['LEAN_PATH']},indent=2));print('PASS',P,flush=True)

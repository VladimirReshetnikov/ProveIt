from pathlib import Path
import os,subprocess,tempfile,hashlib,json,time,shutil,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs');S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency';P=Path(tempfile.mkdtemp(prefix='pra-succ-left-root-'));L=P/'lib/DiophantineConsistency';L.mkdir(parents=True);logs=P/'logs';logs.mkdir();shutil.copyfile(__file__,P/'driver.py')
providers={'PRAFunctionCodes':'/tmp/pra-function-codes-root-ld2dgh6b','PRAFiniteFunctionCodes':'/tmp/pra-finite-function-codes-root-fjtcwus4','PRACodeEncoding':'/tmp/pra-code-encoding-root-e6ee_nqd','PRALanguage':'/tmp/pra-language-root-ugx71zo4','PRATheory':'/tmp/pra-q-current-refresh-5t4dxi2l','PRAAddOne':'/tmp/pra-addcomm-current-g5wd9yz7','PRAAddition':'/tmp/pra-addcomm-current-g5wd9yz7','PRAExhaustion':'/tmp/pra-addcomm-current-g5wd9yz7','PRAOpenInduction':'/tmp/pra-open-zero-root-rc42fm5l','PRAAdditionZeroLeft':'/tmp/pra-open-zero-root-rc42fm5l'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
records=json.loads(Path('/tmp/pra-addcomm-current-g5wd9yz7/state.json').read_text())['records']
for x in records[:3]:
 assert sha(S/(x['module']+'.lean'))==x['source_sha']
 assert sha(Path('/tmp/pra-addcomm-current-g5wd9yz7/lib/DiophantineConsistency')/(x['module']+'.olean'))==x['object_sha']
for n,p in providers.items():
 target=Path(p)/'lib/DiophantineConsistency'/(n+'.olean');(L/(n+'.olean')).symlink_to(target)
(P/'lib/Foundation').symlink_to('/tmp/current-hierarchy2011-author-betz9tp8/lib/Foundation')
names=['PRAAdditionSuccLeft','PRAAdditionSuccLeftChecks'];pins=['511456b6c7b8859001681d8e8196a61c42658baacb3f439201a816470c636e95','dd3817139c3afdf498e5a44c0269d4f8842c37aa9387d59be054d565e3f3ebe1']
for name,pin in zip(names,pins):assert sha(S/(name+'.lean'))==pin;shutil.copyfile(S/(name+'.lean'),logs/(name+'.lean'))
lakepath=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=R,text=True).strip().split(':');package=[p for p in lakepath if '/.lake/packages/' in p or '/.elan/toolchains/' in p];env=dict(os.environ,LEAN_PATH=':'.join([str(P/'lib'),'/tmp/pra-function-codes-root-ld2dgh6b/lib',*package]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
rows=[];print('PRIVATE',P,flush=True)
for name,pin in zip(names,pins):
 p=S/(name+'.lean');assert sha(p)==pin;cmd=['lean','-M6000','-j1','-DElab.async=false','-o',str(L/(name+'.olean')),str(p)];start=time.monotonic()
 with (logs/(name+'.log')).open('w') as f:code=subprocess.run(cmd,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 row=dict(module=name,exit=code,seconds=time.monotonic()-start,source=sha(p),object=sha(L/(name+'.olean')) if (L/(name+'.olean')).exists() else None,log=sha(logs/(name+'.log')));rows.append(row);(P/'state.json').write_text(json.dumps({'status':'RUNNING','rows':rows},indent=2));print(name,code,flush=True);print((logs/(name+'.log')).read_text(),flush=True);assert code==0 and not re.search(r'\b(?:error|warning|sorryAx)\b',(logs/(name+'.log')).read_text());assert sha(p)==pin
(P/'state.json').write_text(json.dumps({'status':'PASS','rows':rows,'lean_path':env['LEAN_PATH'],'providers':{n:sha(L/(n+'.olean')) for n in providers}},indent=2));print('PASS',P,flush=True)

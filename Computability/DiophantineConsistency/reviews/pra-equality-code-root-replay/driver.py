from pathlib import Path
import os,subprocess,tempfile,hashlib,json,time,shutil,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs');S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency';P=Path(tempfile.mkdtemp(prefix='pra-equality-code-root-'));L=P/'lib/DiophantineConsistency';L.mkdir(parents=True);logs=P/'logs';logs.mkdir();shutil.copyfile(__file__,P/'driver.py')
providers={'PRAFunctionCodes':'/tmp/pra-function-codes-root-ld2dgh6b','PRAFiniteFunctionCodes':'/tmp/pra-finite-function-codes-root-fjtcwus4','PRACodeEncoding':'/tmp/pra-code-encoding-root-e6ee_nqd','PRALanguage':'/tmp/pra-language-root-ugx71zo4','PRATheory':'/tmp/pra-q-current-refresh-5t4dxi2l','PRAAddOne':'/tmp/pra-addcomm-current-g5wd9yz7','PRAAddition':'/tmp/pra-addcomm-current-g5wd9yz7','PRAExhaustion':'/tmp/pra-addcomm-current-g5wd9yz7','PRAOpenInduction':'/tmp/pra-open-zero-root-rc42fm5l','PRAAdditionZeroLeft':'/tmp/pra-open-zero-root-rc42fm5l','PRAAdditionSuccLeft':'/tmp/pra-succ-left-root-xz2_a4_i','PRAAdditionCommutativity':'/tmp/pra-add-comm-root-l3pmwssn','PRASubtraction':'/tmp/pra-order-sub-current-s_wv4zty','PRASubSuccCancel':'/tmp/pra-order-sub-current-s_wv4zty','PRASubAddition':'/tmp/pra-order-sub-current-s_wv4zty','PRASubReconstruct':'/tmp/pra-order-sub-current-s_wv4zty','PRAMultiplication':'/tmp/pra-order-current-qjhbjsba','PRANonzero':'/tmp/pra-order-current-qjhbjsba','PRANonzeroCharacter':'/tmp/pra-order-current-qjhbjsba','PRAQCompatibility':'/tmp/pra-order-current-qjhbjsba','PRAQOrder':'/tmp/pra-order-current-v3-fx8s57xa','PRAIsZero':'/tmp/pra-iszero-root-k9akd46o','PRAAdditionZeroLeft':'/tmp/pra-open-zero-root-rc42fm5l','PRABooleanOps':'/tmp/pra-boolean-ops-root-g50rn5m9','PRATermCompilation':'/tmp/pra-term-compilation-root-e3225g5_','PRAOpenFormulaCompiler':'/tmp/pra-open-formula-root-w4g1c006','PRAOpenFormulaCoverage':'/tmp/pra-open-coverage-root-hqtqv9s2'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
records=json.loads(Path('/tmp/pra-addcomm-current-g5wd9yz7/state.json').read_text())['records']
for x in records[:3]:
 assert sha(S/(x['module']+'.lean'))==x['source_sha']
 assert sha(Path('/tmp/pra-addcomm-current-g5wd9yz7/lib/DiophantineConsistency')/(x['module']+'.olean'))==x['object_sha']
for n,p in providers.items():
 target=Path(p)/'lib/DiophantineConsistency'/(n+'.olean');(L/(n+'.olean')).symlink_to(target)
(P/'lib/Foundation').symlink_to('/tmp/current-hierarchy2011-author-betz9tp8/lib/Foundation')
assert sha(S/'PRASubtraction.lean')=='3f9046575346d77d5e816da2b6b147af301d7031216f1839ce645144f70c9e9e'
assert sha(Path('/tmp/pra-order-sub-current-s_wv4zty/lib/DiophantineConsistency/PRASubtraction.olean'))=='aed7210f57f5990c791cc9001af3772662257c28be007f62da9b045f19355ed9'
refreshed=json.loads(Path('/tmp/pra-order-current-qjhbjsba/state.json').read_text());assert refreshed['status']=='PASS'
for x in refreshed['records']:
 assert sha(S/(x['module']+'.lean'))==x['source_sha']
 assert sha(Path('/tmp/pra-order-current-qjhbjsba/lib/DiophantineConsistency')/(x['module']+'.olean'))==x['object_sha']
refreshed2=json.loads(Path('/tmp/pra-order-sub-current-s_wv4zty/state.json').read_text());assert refreshed2['status']=='PASS'
for x in refreshed2['records']:
 if x['module']=='PRAQOrder':continue
 assert sha(S/(x['module']+'.lean'))==x['source_sha']
 assert sha(Path('/tmp/pra-order-sub-current-s_wv4zty/lib/DiophantineConsistency')/(x['module']+'.olean'))==x['object_sha']
refreshed3=json.loads(Path('/tmp/pra-order-current-v3-fx8s57xa/state.json').read_text());assert refreshed3['status']=='PASS'
for x in refreshed3['records']:
 assert sha(S/(x['module']+'.lean'))==x['source_sha']
 assert sha(Path('/tmp/pra-order-current-v3-fx8s57xa/lib/DiophantineConsistency')/(x['module']+'.olean'))==x['object_sha']
names=['PRASubSuccessorInvariant','PRASubSuccessorInvariantChecks','PRAEqualityDifference','PRAEqualityDifferenceChecks','PRAEqualityCode','PRAEqualityCodeChecks'];pins=['b5773abdfe5085e148efdfaafa8b1b9c14877239c9ed13299bab9bf03f0fdf59','7b542ac3f07c0e9f6f2dffcecd9118f9c2db125f93f23f7482ca9cf35f11fc30','e8fd3dfca64d18d484aa0edd5503b9b1966aca5fc929c8843c1712da8c76cf97','64486aa78d21c8ee4c09d743a60509eb946709812b07cebd8997b4dbccfac244','5ede4f3aea932d355768b2840eabafd40fe96bdf0bb1c28e818fbae4b9206b96','f32918a8bf98e769db452fb516130fc5b3a8036d1813ae2f48323d02a0e6fa47']
for name,pin in zip(names,pins):assert sha(S/(name+'.lean'))==pin;shutil.copyfile(S/(name+'.lean'),logs/(name+'.lean'))
lakepath=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=R,text=True).strip().split(':');package=[p for p in lakepath if '/.lake/packages/' in p or '/.elan/toolchains/' in p];env=dict(os.environ,LEAN_PATH=':'.join([str(P/'lib'),'/tmp/pra-function-codes-root-ld2dgh6b/lib',*package]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
rows=[];print('PRIVATE',P,flush=True)
for name,pin in zip(names,pins):
 p=S/(name+'.lean');assert sha(p)==pin;cmd=['lean','-M6000','-j1','-DElab.async=false','-o',str(L/(name+'.olean')),str(p)];start=time.monotonic()
 with (logs/(name+'.log')).open('w') as f:code=subprocess.run(cmd,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 row=dict(module=name,exit=code,seconds=time.monotonic()-start,source=sha(p),object=sha(L/(name+'.olean')) if (L/(name+'.olean')).exists() else None,log=sha(logs/(name+'.log')));rows.append(row);(P/'state.json').write_text(json.dumps({'status':'RUNNING','rows':rows},indent=2));print(name,code,flush=True);print((logs/(name+'.log')).read_text(),flush=True);assert code==0 and not re.search(r'\b(?:error|warning|sorryAx)\b',(logs/(name+'.log')).read_text());assert sha(p)==pin
(P/'state.json').write_text(json.dumps({'status':'PASS','rows':rows,'lean_path':env['LEAN_PATH'],'providers':{n:sha(L/(n+'.olean')) for n in providers}},indent=2));print('PASS',P,flush=True)

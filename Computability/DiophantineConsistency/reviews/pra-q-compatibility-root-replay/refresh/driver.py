from pathlib import Path
import hashlib,json,os,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
old=Path('/tmp/pra-q-compat-author-ihfc8jl8/lib');root=Path(tempfile.mkdtemp(prefix='pra-q-current-refresh-'));lib=root/'lib';lib.mkdir(); dst=lib/'DiophantineConsistency';dst.mkdir();(lib/'Foundation').symlink_to((old/'Foundation').resolve(),target_is_directory=True);logs=root/'logs';logs.mkdir()
names=['PRATheory','PRAAddOne','PRAAddition','PRAMultiplication','PRAExhaustion']; sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
for f in (old/'DiophantineConsistency').glob('*.olean'):
 if f.stem not in names and f.stem!='PRAQCompatibility':(dst/f.name).symlink_to(f.resolve())
for n in names:(logs/(n+'.lean')).write_bytes((S/(n+'.lean')).read_bytes())
search=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=R,text=True).strip();env=dict(os.environ,LEAN_PATH=str(lib)+':'+search,LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
state={'status':'RUNNING','private':str(root),'records':[],'input_sources':{n:sha(S/(n+'.lean')) for n in names},'LEAN_PATH':env['LEAN_PATH']};(root/'state.json').write_text(json.dumps(state,indent=2));Path('/tmp/pra-q-current-refresh-location').write_text(str(root)+'\n')
for n in names:
 src=S/(n+'.lean'); assert sha(src)==state['input_sources'][n] and sha(logs/(n+'.lean'))==sha(src)
 cmd=['lean','-M6000','-j1','-DElab.async=false',str(src),'-o',str(dst/(n+'.olean'))]; start=time.monotonic()
 with (logs/(n+'.log')).open('w') as f: p=subprocess.run(cmd,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT)
 row={'module':n,'command':cmd,'code':p.returncode,'seconds':time.monotonic()-start,'source_sha':sha(src),'log_sha':sha(logs/(n+'.log')),'object_sha':sha(dst/(n+'.olean')) if (dst/(n+'.olean')).is_file() else None};state['records'].append(row);(root/'state.json').write_text(json.dumps(state,indent=2));print(n,p.returncode,flush=True)
 if p.returncode or (logs/(n+'.log')).read_text():state['status']='FAILED';(root/'state.json').write_text(json.dumps(state,indent=2));raise SystemExit(1)
for n in names:assert sha(S/(n+'.lean'))==state['input_sources'][n]
state['status']='PASS';(root/'state.json').write_text(json.dumps(state,indent=2));print('PASS',root,flush=True)

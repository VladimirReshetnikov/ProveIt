"""Read-only complete post-build authentication of the Assembly branch."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile
R=Path('/home/codex/.codex/worktrees/46be/Proofs');P=Path(os.environ.get('ASSEMBLY_COMPAT_BUILD','/tmp/adaptive-assembly-compat-7ths2hw9'));S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency';A=R/'Computability/DiophantineConsistency/research/wang-chunk-full/reauth_cell_compat.py';T=R/'Computability/DiophantineConsistency/research/wang-chunk-full/audit_reduced_provider.py';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text());ps=read(P/'state.json');assert ps['status']=='PASS' and len(ps['records'])==8;D=Path(ps['cell_provider']);X=Path(ps['reduced_audit']);xs=read(X/'state.json');assert xs['status']=='PASS' and sha(X/'result.json')==ps['reduced_audit_result_sha256'];ph=sha(P/'state.json');ah=sha(A);th=sha(T)
def outputs():
 if sha(P/'state.json')!=ph or sha(D/'state.json')!=ps['cell_state_sha256'] or sha(X/'state.json')!=ps['reduced_audit_state_sha256'] or sha(X/'result.json')!=ps['reduced_audit_result_sha256'] or sha(A)!=ah or sha(T)!=th:return False
 return all(r['exit']==0 and sha(S/(r['name']+'.lean'))==sha(P/'logs'/(r['name']+'.lean'))==r['source_sha256'] and sha(P/'lib/DiophantineConsistency'/(r['name']+'.olean'))==r['object_sha256'] and sha(P/'logs'/(r['name']+'.log'))==r['log_sha256'] and sha(P/'logs'/(r['name']+'.time'))==r['time_sha256'] for r in ps['records'])
assert outputs();w=Path(tempfile.mkdtemp(prefix='adaptive-assembly-compat-reauth-'));shutil.copyfile(__file__,w/'driver.py');state={'status':'RUNNING','private':str(w),'assembly_build':str(P),'assembly_state_sha256':ph,'record_count':8,'scope':'Read-only postcheck of eight sources, objects and logs plus full inherited CellWindow and reduced-provider authentication; no HA proof or canonical integration.'};save=lambda:(w/'state.json').write_text(json.dumps(state,indent=2)+'\n');save();print('PRIVATE',w,flush=True)
try:
 for label,script,env in [('cell',A,dict(os.environ,CELL_COMPAT_BUILD=str(D))),('reduced',T,dict(os.environ))]:
  q=subprocess.run(['python3',str(script)],cwd=R,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);(w/(label+'.log')).write_text(q.stdout);assert q.returncode==0,q.stdout;lines=[x for x in q.stdout.splitlines() if x.startswith('PASS ')];assert len(lines)==1;z=Path(lines[0].split()[1]);zs=read(z/'state.json');assert zs['status']=='PASS'
  if label=='reduced':assert zs['result_sha256']==ps['reduced_audit_result_sha256']
  shutil.copyfile(z/'state.json',w/(label+'.json'));state[label]={'audit_path':str(z),'log_sha256':sha(w/(label+'.log')),'state_sha256':sha(w/(label+'.json'))};save();print('AUTH',label,z,flush=True)
 assert outputs();state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise

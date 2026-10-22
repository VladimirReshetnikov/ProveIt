"""Record three authorized metadata-only invocations and immutable input pins."""
from pathlib import Path
import datetime,hashlib,json,subprocess,time
S=Path('/tmp/k215-phase13-publication');D=Path(__file__).resolve().parent;R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
save=lambda p,x:p.write_text(json.dumps(x,indent=2)+'\n')
freeze=json.loads((S/'freeze.json').read_text());assert sha(S/'freeze.json')=='d7ae992e234a3d35656998ea6f724c64e59a3c6a0ff47ae326686c76f784c649'
peer=Path('/tmp/k215-phase13-publication-peer/review-v2.json');assert sha(peer)=='f7db65908bbc1e99987ca76a7d191a00b4b26d604f356a5083023abe2972f882'
inputs={str(S/n):p for n,p in freeze['files'].items()};inputs[str(S/'freeze.json')]=sha(S/'freeze.json');inputs[str(peer)]=sha(peer);inputs[str(Path(__file__))]=sha(__file__)
inputs.update({p:r['sha256']for p,r in json.loads((S/'config.json').read_text())['files'].items()})
def recheck():
 for p,pin in inputs.items():assert sha(p)==pin,p
recheck();save(D/'before.json',{'status':'PINNED_BEFORE_OWN_METADATA_EXECUTION','inputs':inputs})
jobs=[('controls',['python3','-B',str(S/'controls.py'),'--output',str(S/'controls-result.json')],S/'controls.stdout.log',S/'controls.stderr.log'),('collect',['python3','-B',str(S/'collect.py'),'--basis-repo',str(R),'--out',str(S/'staged-lean')],D/'collect.stdout.log',D/'collect.stderr.log'),('saved',['python3','-B',str(S/'staged-lean/review_saved.py'),'--basis-repo',str(R),'--repo',str(R),'--output',str(S/'staged-lean/saved-review.json')],D/'saved.stdout.log',D/'saved.stderr.log')]
records=[]
for name,cmd,out,err in jobs:
 assert not out.exists()and not err.exists();recheck();start=time.monotonic();started=datetime.datetime.now(datetime.timezone.utc).isoformat()
 with out.open('wb')as stdout,err.open('wb')as stderr:result=subprocess.run(cmd,cwd=R,stdout=stdout,stderr=stderr)
 row={'job':name,'command':cmd,'cwd':str(R),'exit_code':result.returncode,'seconds':time.monotonic()-start,'started_utc':started,'stdout':str(out),'stderr':str(err),'stdout_sha256':sha(out),'stderr_sha256':sha(err),'wrapper_sha256':sha(__file__),'helper_freeze_sha256':sha(S/'freeze.json')}
 recheck();row['all_pinned_inputs_unchanged']=True;records.append(row);save(D/(name+'-actual.json'),row);save(D/'actual.json',{'status':'PASS'if len(records)==3 and all(r['exit_code']==0 for r in records)else'INCOMPLETE_OR_FAILED','jobs':records,'inputs':inputs,'scope':'Own controls/collector/saved reader only; no proof compiler, producer or supplied script invocation.'});print(name,'exit',result.returncode,round(row['seconds'],3),flush=True)
 if result.returncode:raise SystemExit(result.returncode)
recheck();print('COMPLETE metadata publication',flush=True)

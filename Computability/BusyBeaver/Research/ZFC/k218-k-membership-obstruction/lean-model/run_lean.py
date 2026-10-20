from pathlib import Path
import argparse,hashlib,json,os,subprocess,time
p=argparse.ArgumentParser();p.add_argument('attempt');a=p.parse_args()
base=Path(__file__).resolve().parent;out=base/a.attempt;out.mkdir()
parent=Path('/tmp/zfc-positive-simulation/run4/verification.json');e=json.loads(parent.read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
src=base/'KRABModel.lean';snap=out/src.name;snap.write_bytes(src.read_bytes())
q=next(x for x in e['reused_modules'] if x['module']=='BusyBeaver.ZFC.Code254')
assert sha(q['source'])==q['source_sha256'] and sha(q['object'])==q['object_sha256']
compiler=e['compiler']['path'];assert sha(compiler)==e['compiler']['sha256']
cmd=[compiler,'-j1','-M4096','-o',str(out/'KRABModel.olean'),str(snap)]
env=dict(os.environ,LEAN_PATH=e['LEAN_PATH'],LEAN_NUM_THREADS='1')
r={'status':'RUNNING','source_sha256':sha(src),'source_snapshot':str(snap),'command':cmd,'timeout_seconds':120,'parent':{'path':str(parent),'sha256':sha(parent)},'selected_Code254':q,'LEAN_PATH':env['LEAN_PATH'],'scope':'New source only; inherited cached namespace is a boundary, no transitive dependency replay or new version query.'}
(out/'result.json').write_text(json.dumps(r,indent=2)+'\n');t=time.monotonic()
try:
 z=subprocess.run(cmd,env=env,cwd=base,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=120)
 log=z.stdout;r.update(status='PASS' if z.returncode==0 else 'FAIL',exit_code=z.returncode)
except subprocess.TimeoutExpired as ex:
 log=ex.stdout or '';log=log.decode() if isinstance(log,bytes) else log;r.update(status='TIMEOUT',exit_code=None)
(out/'source.log').write_text(log);r.update(seconds=time.monotonic()-t,log_sha256=sha(out/'source.log'))
if (out/'KRABModel.olean').exists():r['object_sha256']=sha(out/'KRABModel.olean')
(out/'result.json').write_text(json.dumps(r,indent=2)+'\n')
print(log);print(json.dumps({k:v for k,v in r.items() if k in ['status','exit_code','seconds','source_sha256']},indent=2))

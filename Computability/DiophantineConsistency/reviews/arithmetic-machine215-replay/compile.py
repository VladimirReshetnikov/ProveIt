from pathlib import Path
import hashlib,json,os,subprocess,sys,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');W=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
dp=W/'dependencies-current.json'; d=json.loads((dp if dp.exists() else W/'dependencies.json').read_text());m=json.load(open('/tmp/current-positive-zero2011-closure-plan/manifest.json'))
assert sha(d['compiler']['path'])==d['compiler']['sha256']
for x in d['modules']:
 if x['module']=='DiophantineConsistency.DecimalMachine215' and not dp.exists():
  assert sha(x['source'])==json.loads((W/'DecimalMachine215-import-only.json').read_text())['new_sha256']
 else: assert sha(x['source'])==x['source_sha256'],x['module']
 for o in x['objects']:assert sha(o['path'])==o['sha256'],o['path']
name=sys.argv[1];stage=sys.argv[2]
assert name in ['ArithmeticMachine'+k+'215'+s for k in ['Graph','Step','Run'] for s in ['','Checks']]+['DecimalMachine215','DecimalMachine215Checks']
assert stage.isalnum()
src=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'/(name+'.lean')
output=W/'lib/DiophantineConsistency'/(name+'.olean');output.parent.mkdir(exist_ok=True,parents=True)
if output.is_symlink():
 assert name=='DecimalMachine215'
 output.unlink()
log=W/(name+'-'+stage+'.log');timing=log.with_suffix('.time');state=W/(name+'-'+stage+'.json');assert not log.exists()
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(W/'lib')]+m['external_lean_path']);env.pop('LEAN_SRC_PATH',None)
cmd=['/usr/bin/time','-f','elapsed=%e max_rss_kb=%M','-o',str(timing),d['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(output),str(src)]
x={'source':str(src),'source_sha256':sha(src),'command':cmd,'started':time.time(),'log':str(log),'LEAN_PATH':env['LEAN_PATH']}
with log.open('w') as f:
 p=subprocess.Popen(cmd,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT);x['pid']=p.pid;state.write_text(json.dumps(x,indent=2));code=p.wait()
x.update(exit_code=code,finished=time.time(),log_sha256=sha(log),timing_sha256=sha(timing))
assert sha(src)==x['source_sha256']
if code==0:x.update(object=str(output),object_sha256=sha(output))
state.write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x));print(log.read_text());sys.exit(code)

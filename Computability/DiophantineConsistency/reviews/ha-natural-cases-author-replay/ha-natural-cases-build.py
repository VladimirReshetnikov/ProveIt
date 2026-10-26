from pathlib import Path
import json,hashlib,os,subprocess,sys,time
root=Path('/home/codex/.codex/worktrees/46be/Proofs')
out=Path('/tmp/ha-natural-cases-current').read_text().strip(); out=Path(out)
a=json.loads((out/'inputs.json').read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
for p in a['pins']: assert sha(p['path'])==p['sha256'],p['path']
name=sys.argv[1]; stage=sys.argv[2]
assert name in ['HANaturalCases','HANaturalCasesChecks']
src=root/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'/f'{name}.lean'
obj=Path(a['lib'])/'DiophantineConsistency'/f'{name}.olean'
assert not obj.is_symlink()
(out/f'{name}-{stage}.lean').write_bytes(src.read_bytes())
cmd=[a['compiler'],'-M6000','-j1','-DElab.async=false',str(src),'-o',str(obj)]
env=os.environ.copy();env['LEAN_PATH']=a['lib']
start=time.time()
with (out/f'{name}-{stage}.log').open('w') as log:r=subprocess.run(cmd,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT)
for p in a['pins']: assert sha(p['path'])==p['sha256'],p['path']
result=dict(module=name,source=str(src),source_sha256=sha(src),command=cmd,lean_path=env['LEAN_PATH'],exit_code=r.returncode,elapsed_seconds=time.time()-start,log=str(out/f'{name}-{stage}.log'),log_sha256=sha(out/f'{name}-{stage}.log'))
if r.returncode==0:result.update(object=str(obj),object_sha256=sha(obj))
(out/f'{name}-{stage}.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2));print((out/f'{name}-{stage}.log').read_text());sys.exit(r.returncode)

from pathlib import Path
import json,hashlib,shutil,os,tempfile,subprocess,time,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs');old=Path('/tmp/dag-controlperm222-controller-author-vm261dx4')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rec(p):return dict(path=str(p),sha256=sha(p))
j=json.loads((old/'inputs.json').read_text());st=json.loads((old/'AUTHOR.json').read_text());assert sha(old/'inputs.json')==st['inputs']['sha256']
for pin in j['pins']:assert sha(pin['path'])==pin['sha256']
assert shutil.disk_usage('/tmp').free>=512*1024**2
p=Path(tempfile.mkdtemp(prefix='dag-controlperm222-generic-prefix-'))
source=R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticDagControlPerm222.lean';full=source.read_text();prefix=full.split('private theorem catalogue_length',1)[0]
text=prefix+'\n#print axioms entryAt_eq\n#print axioms rowAt_eq\n#print axioms packedAt_eq\nend SetTheory.BusyBeaver.ZFC.ArithmeticDagControlPerm222\n'
src=p/'GenericPrefix.lean';src.write_text(text);shutil.copyfile(source,p/'FullSource.lean')
out=p/'GenericPrefix.olean';log=p/'GenericPrefix.log';timing=p/'GenericPrefix.time'
cmd=[j['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),str(src)]
env=dict(os.environ,LEAN_PATH=j['lean_path'],LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
start=time.monotonic()
with log.open('w')as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
result=dict(scope='Diagnostic exact generic prefix only, no full catalogue/occurrence/endpoint claimed. Object is never imported by final modules.',base_inputs=rec(old/'inputs.json'),driver=rec(__file__),full_source=rec(source),snapshot=rec(p/'FullSource.lean'),source=rec(src),command=cmd,exit_code=code,seconds=time.monotonic()-start,log=rec(log),timing=rec(timing),private=str(p))
if out.exists():result['object']=rec(out)
assert sha(source)==sha(p/'FullSource.lean')
(p/'PREFIX.json').write_text(json.dumps(result,indent=2)+'\n');print(str(p));print(log.read_text());raise SystemExit(code)

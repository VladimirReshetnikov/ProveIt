"""Replay the six October 10 continuations in isolated delivered layouts."""
from pathlib import Path
import argparse, hashlib, json, os, shutil, subprocess, sys, time

B=Path(__file__).resolve().parents[1]
names={'rank':'level4-rank-proof','cm-zero':'relation-cm-zero-transitions',
       'formal':'formal-reductions-continuation','angular':'angular-zero-continuation',
       'cayley':'cayley-s4-continuation','lerch':'lerch-zero-bifurcations'}
ap=argparse.ArgumentParser();ap.add_argument('--part',choices=names,required=True)
a=ap.parse_args();source=B.parent/'reports'/names[a.part]
root=B/'verification/.scratch-research'/a.part
out=B/'verification/research-replay'/a.part
root.parent.mkdir(parents=True,exist_ok=True);out.mkdir(parents=True,exist_ok=True)
shutil.copytree(source,root,dirs_exist_ok=True,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
start=time.time_ns();runs=[]
def run(program,*args):
    env=dict(os.environ,PYTHONUTF8='1',PYTHONDONTWRITEBYTECODE='1',PYTHONPATH=str(root))
    p=subprocess.run([sys.executable,str(root/program),*args],cwd=root,env=env,
                     capture_output=True,text=True,encoding='utf-8',errors='replace')
    (out/(Path(program).stem+'-run.txt')).write_text((p.stdout+p.stderr).rstrip()+'\n',encoding='utf-8')
    runs.append(dict(program=program,arguments=list(args),exit_code=p.returncode))
    print(a.part,program,'exit',p.returncode,flush=True)
    if p.returncode:raise RuntimeError('Replay failed; inspect '+str(out))
if a.part=='rank':run('code/verify.py');run('code/numerics.py')
elif a.part=='cm-zero':run('code/verify_all.py')
elif a.part=='formal':run('code/run_checks.py')
elif a.part=='angular':run('code/run_verification.py','--receipt',str(root/'fresh-receipt.json'),'--log',str(root/'fresh-run.log'))
elif a.part=='cayley':
    for f in ['verify_s4.py','verify_s4_independent.py','test_kernels.py','verify_receipts.py']:run('code/'+f)
else:
    run('verification/certify.py');run('verification/test_exact.py')
fresh=[]
for p in sorted(root.rglob('*.json')):
    if p.stat().st_mtime_ns<start:continue
    rel=p.relative_to(root);q=out/rel;q.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(p,q);fresh.append(rel.as_posix())
manifest={p.relative_to(source).as_posix():hashlib.sha256(p.read_bytes()).hexdigest()
          for p in sorted(source.rglob('*.py'))}
(out/'replay-summary.json').write_text(json.dumps(dict(part=a.part,source_folder=names[a.part],
    source_code_sha256=manifest,commands=runs,fresh_result_files=fresh,
    passed=all(c['exit_code']==0 for c in runs),scope='Exact certificates and numerical diagnostics retain their separate scientific scopes; analytic proofs require an independent manuscript audit.'),indent=2)+'\n',encoding='utf-8')
print(a.part,'completed;',len(fresh),'fresh JSON receipts.')

"""Replay the five later research packages in isolated delivered layouts."""
from pathlib import Path
import argparse, hashlib, json, os, shutil, subprocess, sys, time
B=Path(__file__).resolve().parents[1]
names={'herglotz':'herglotz-rational-classification','phase':'lerch-global-phase',
       'uniform':'uniform-transition-continuation','boundary':'lerch-boundary-continuation',
       'signed':'zero-cm-signed-continuation'}
ap=argparse.ArgumentParser();ap.add_argument('--part',choices=names,required=True)
a=ap.parse_args();source=B.parent/'reports'/names[a.part]
root=B/'verification/.scratch-third'/a.part;out=B/'verification/third-replay'/a.part
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
    if p.returncode:raise RuntimeError('Replay failed: '+str(out))
if a.part=='herglotz':run('code/verify_exact.py','--bound','500');run('code/verify_numeric.py','--dps','90','140')
elif a.part=='phase':run('code/verify_exact.py');run('code/test_exact.py')
elif a.part=='uniform':run('verify.py','--receipt',str(root/'fresh-receipt.json'))
elif a.part=='boundary':
    for name in ['certify.py','certify_minimum.py','test_algebra.py','test_integration.py']:run('verification/'+name)
else:run('code/replay_exact.py')
fresh=[]
for p in sorted(root.rglob('*.json')):
    if p.stat().st_mtime_ns<start:continue
    rel=p.relative_to(root);q=out/rel;q.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(p,q);fresh.append(rel.as_posix())
manifest={p.relative_to(source).as_posix():hashlib.sha256(p.read_bytes()).hexdigest()
          for p in sorted(source.rglob('*.py'))}
(out/'replay-summary.json').write_text(json.dumps(dict(part=a.part,source_folder=names[a.part],
    source_code_sha256=manifest,commands=runs,fresh_result_files=fresh,
    passed=all(c['exit_code']==0 for c in runs),scope='Exact replay and numerical diagnostics keep their separate evidence scopes. General analytic claims require manuscript audit.'),indent=2)+'\n',encoding='utf-8')
print(a.part,'completed;',len(fresh),'fresh JSON receipts.')

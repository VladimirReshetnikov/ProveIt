"""Fresh real-order density and geometry diagnostics in immutable-layout copies."""
from pathlib import Path
import argparse, hashlib, json, os, shutil, subprocess, sys, time
B=Path(__file__).resolve().parents[1]
names={'threshold':'real-order-threshold','geometry':'finite-golden-uniform-continuation',
       'boundary':'finite-golden-uniform-continuation'}
ap=argparse.ArgumentParser();ap.add_argument('--part',choices=names,required=True)
a=ap.parse_args();source=B.parent/'reports'/names[a.part]
root=B/'verification/.scratch-real-orders'/a.part
out=B/'verification/real-order-replay'/a.part
root.parent.mkdir(parents=True,exist_ok=True);out.mkdir(parents=True,exist_ok=True)
shutil.copytree(source,root,dirs_exist_ok=True,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
started=time.time_ns();commands=[]
programs=['audit.py','critical_identities.py','certify.py'] if a.part=='threshold' else [
    'geometry_diagnostics.py' if a.part=='geometry' else 'geometry_boundary_diagnostics.py']
for name in programs:
    program=root/'code'/name
    env=dict(os.environ,PYTHONUTF8='1',PYTHONIOENCODING='utf-8',PYTHONDONTWRITEBYTECODE='1')
    p=subprocess.run([sys.executable,str(program)],cwd=root,env=env,
                     capture_output=True,text=True,encoding='utf-8',errors='replace')
    (out/(program.stem+'-run.txt')).write_text((p.stdout+p.stderr).rstrip()+'\n',encoding='utf-8')
    commands.append(dict(program='code/'+name,exit_code=p.returncode))
    print(a.part,name,'exit',p.returncode,flush=True)
    if p.returncode:raise RuntimeError('Replay failed: '+str(out))
fresh=[]
for p in sorted(root.rglob('*.json')):
    if p.stat().st_mtime_ns<started:continue
    rel=p.relative_to(root);q=out/rel;q.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(p,q);fresh.append(rel.as_posix())
manifest={p.relative_to(source).as_posix():hashlib.sha256(p.read_bytes()).hexdigest()
          for p in sorted(source.rglob('*.py'))}
(out/'replay-summary.json').write_text(json.dumps(dict(part=a.part,source_folder=names[a.part],
    source_code_sha256=manifest,commands=commands,fresh_result_files=fresh,
    passed=all(c['exit_code']==0 for c in commands),
    scope='Symbolic identities, exact fractional certificates and separately labeled density/geometry/boundary diagnostics. Analytic proofs and universal claims require the manuscript arguments.'),indent=2)+'\n',encoding='utf-8')
print(a.part,'completed;',len(fresh),'fresh JSON receipts.')

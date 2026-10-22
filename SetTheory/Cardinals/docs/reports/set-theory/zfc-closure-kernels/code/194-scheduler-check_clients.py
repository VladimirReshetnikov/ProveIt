#!/usr/bin/env python3
"""Check local scheduler overlays against a freshly checked provider receipt."""
from pathlib import Path
import argparse, hashlib, json, os, shutil, subprocess, time

p=argparse.ArgumentParser()
p.add_argument('--repo',type=Path,required=True)
p.add_argument('--lean',type=Path,required=True)
p.add_argument('--providers',type=Path,required=True)
p.add_argument('--overlay',type=Path,required=True)
p.add_argument('--out',type=Path,required=True)
a=p.parse_args()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
a.repo=a.repo.resolve(); a.overlay=a.overlay.resolve(); a.out=a.out.resolve(); a.providers=a.providers.resolve()
data=json.loads((a.providers/'providers.json').read_text())
for row in data['modules']:
    assert row['exit_code']==0
    assert sha(a.repo/row['source'])==row['source_sha256'],row['module']
    assert sha(a.providers/(row['module'].replace('.','/')+'.olean'))==row['olean_sha256'],row['module']
    assert sha(a.providers/row['log'])==row['log_sha256'],row['module']
version=subprocess.check_output([str(a.lean),'--version'],text=True).strip()
assert version==data['lean_version']
objects=a.out/'objects'; logs=a.out/'logs'
objects.mkdir(parents=True,exist_ok=True); logs.mkdir(parents=True,exist_ok=True)
for row in data['modules']:
    rel=Path(row['module'].replace('.','/')+'.olean')
    destination=objects/rel
    destination.parent.mkdir(parents=True,exist_ok=True)
    shutil.copy2(a.providers/rel,destination)
env=dict(os.environ,LEAN_PATH=str(objects))
rows=[]
for short in ['CofinalScheduler','EnumPerm','Enum254','Enum222','EnumDom','SchedulerAudit']:
    name='BusyBeaver.ZFC.'+short
    rel=Path(name.replace('.','/')+'.lean')
    src=a.overlay/rel
    out=objects/rel.with_suffix('.olean'); out.parent.mkdir(parents=True,exist_ok=True)
    tick=time.monotonic()
    result=subprocess.run([str(a.lean),'-o',str(out),str(rel)],cwd=a.overlay,env=env,text=True,capture_output=True)
    log=logs/(name+'.log'); log.write_text(result.stdout+result.stderr)
    row={'module':name,'source':str(rel),'source_sha256':sha(src),'exit_code':result.returncode,
      'seconds':round(time.monotonic()-tick,3),'log':'logs/'+log.name,'log_sha256':sha(log),
      'olean_sha256':sha(out) if out.exists() else None,'output':result.stdout+result.stderr}
    rows.append(row)
    print(name,result.returncode,row['seconds'],flush=True)
    if result.returncode or 'sorryAx' in row['output'] or "declaration uses 'sorry'" in row['output']:
        print(row['output'],flush=True)
        break
receipt={'lean_version':version,'lean_binary_sha256':sha(a.lean),'providers_receipt_sha256':sha(a.providers/'providers.json'),'modules':rows}
(a.out/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
assert len(rows)==6 and all(r['exit_code']==0 for r in rows),'build failed'

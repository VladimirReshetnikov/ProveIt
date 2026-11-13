#!/usr/bin/env python3
"""Point-in-time workspace/staged source comparison; never writes build paths."""
import hashlib
import json
import subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];TASK=ROOT/'Computability/DiophantineConsistency'
PLAN=TASK/'research/current14-printed-port-extension-plan';BASE=Path('/tmp/current14-standard-fresh-source-20261104')
STAGED=Path('/tmp/current14-printed-port-extension-v3-20261104/src');OUT=HERE/'source-audit-after-p57-root.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(c,m):
    if not c:raise ValueError(m)
def read(p):return json.loads(Path(p).read_text())
need(not OUT.exists(),'refusing existing output')
pins={'kernel-manifest.json':'4809f9cb3572bb0bdc47b22fd6a0c0e277c215d7aa322fd1847e8e63152fd6b2',
      'masks-manifest.json':'7e6d83edfa707b63e1ad1f6070cad00d01859929dca4a9459063af5e0932a8ff',
      'result.json':'cb1817489d0ea7ca5cb3f805acd857a7e22e68659fc664e03b8360d70f4f231c'}
for n,h in pins.items():need(sha(PLAN/n)==h,('plan drift',n))
need(sha(BASE/'manifest.json')=='1e8b03cac1b2db995091dff13c749faf955fc524bf2da42a637743e9d7a53749','base manifest drift')
base=read(BASE/'manifest.json');rows={}
for fn in ('kernel-manifest.json','masks-manifest.json'):
    for name,row in read(PLAN/fn)['sources'].items():
        if name in rows:need(rows[name]['sha256']==row['sha256'] and rows[name]['imports']==row['imports'],('plan source conflict',name))
        rows[name]=row
order=read(PLAN/'result.json')['extra_project_build_order'];shared=set(rows)&set(base['sources'])
need(len(rows)==84 and len(shared)==23 and len(order)==len(set(order))==61 and set(order)==set(rows)-shared,'closure count mismatch')
paths=[]
for name,row in rows.items():
    path=ROOT/row['workspace_path'];paths.append(row['workspace_path']);need(path.is_file() and sha(path)==row['sha256'],('workspace drift',name))
    if name in shared:
        br=base['sources'][name];need(br['sha256']==row['sha256'] and br['imports']==row['imports'] and sha(BASE/br['snapshot_path'])==row['sha256'],('base shared drift',name))
    else:
        staged=STAGED/(name.replace('.','/')+'.lean');need(staged.is_file() and not staged.is_symlink() and sha(staged)==row['sha256'],('staged source drift',name))
def gitset(*args):return {p.decode() for p in subprocess.check_output(['git',*args,'--',*paths],cwd=ROOT).split(b'\0') if p}
need(gitset('ls-files','-z')==set(paths),'sources no longer all tracked')
need(not gitset('diff','--name-only','-z','HEAD'),'workspace source differs from HEAD')
for name,row in rows.items():need(sha(ROOT/row['workspace_path'])==row['sha256'],('source drift during audit',name))
result={'status':'PASS_POINT_IN_TIME_SOURCE_AUDIT','head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
        'project_sources':84,'shared_base_sources':23,'staged_extra_sources':61,'changed':[],'untracked':[],
        'audit_sha256':sha(__file__),'scope':'Source bytes, Git tracking and plan-declared shared imports only; not a process, output or transitive-provider audit.'}
with OUT.open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
print(json.dumps(result,sort_keys=True))

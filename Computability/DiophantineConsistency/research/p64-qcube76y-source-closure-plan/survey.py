#!/usr/bin/env python3
"""Plan only: source-declared 76Y endpoint closure and fresh-base comparison."""
import hashlib
import json
import re
import subprocess
import sys
import tomllib
from collections import defaultdict
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
TASK=ROOT/'Computability/DiophantineConsistency'
BASE=TASK/'research/current14-standard-fresh-rebuild-preflight/snapshot-manifest.json'
OUT=HERE/'result.json'
BASE_SHA='1e8b03cac1b2db995091dff13c749faf955fc524bf2da42a637743e9d7a53749'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
if sha(BASE)!=BASE_SHA:raise RuntimeError('base manifest pin mismatch')
base=json.loads(BASE.read_text())
cfg=tomllib.loads((ROOT/'lakefile.toml').read_text())
libs={x['name']:ROOT/x.get('srcDir','.') for x in cfg['lean_lib'] if x['name']!='Foundation'}
paths=subprocess.check_output(['rg','--files',str(TASK/'research'),'-g','*.lean'],text=True).splitlines()
index=defaultdict(list)
for name in paths:
    path=Path(name)
    if '/observations/' not in str(path):index[path.stem].append(path)
def strip_comments(s):
    out=[];i=0;depth=0;string=False
    while i<len(s):
        if depth:
            if s.startswith('/-',i):depth+=1;i+=2
            elif s.startswith('-/',i):depth-=1;i+=2
            else:out.append('\n' if s[i]=='\n' else ' ');i+=1
        elif string:
            if s[i]=='\\':out.extend('  ');i+=2
            elif s[i]=='"':out.append(' ');i+=1;string=False
            else:out.append('\n' if s[i]=='\n' else ' ');i+=1
        elif s.startswith('/-',i):depth=1;i+=2
        elif s.startswith('--',i):
            while i<len(s) and s[i]!='\n':i+=1
        elif s[i]=='"':string=True;out.append(' ');i+=1
        else:out.append(s[i]);i+=1
    if depth or string:raise ValueError('unterminated comment or string')
    return ''.join(out)
def imports(path):
    out=[]
    for line in strip_comments(path.read_text()).splitlines():
        m=re.fullmatch(r'\s*(?:(?:public|meta)\s+)*import\s+(.+?)\s*',line)
        if m:
            names=m.group(1).split()
            if any(not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*",n) for n in names):raise ValueError(('unsupported import',str(path),line))
            out.extend(names)
    return out
rows={};external=set();visiting=set();order=[]
def visit(name):
    if name in rows or name in external:return
    if name in visiting:raise ValueError(('cycle',name))
    top=name.split('.')[0]
    if top in libs:
        kind='project';path=libs[top]/(name.replace('.','/')+'.lean')
        if not path.is_file():raise FileNotFoundError((name,str(path)))
    elif '.' not in name and name in index:
        candidates=index[name]
        if len(candidates)!=1:raise ValueError(('ambiguous flat source',name,[str(p) for p in candidates]))
        kind='local';path=candidates[0]
    else:external.add(name);return
    raw=path.read_bytes(); h=hashlib.sha256(raw).hexdigest();deps=imports(path)
    if sha(path)!=h:raise RuntimeError(('source changed',name))
    visiting.add(name)
    for dep in deps:visit(dep)
    visiting.remove(name)
    rows[name]={'kind':kind,'path':str(path.relative_to(ROOT)),'sha256':h,'imports':deps}
    order.append(name)
visit('P64QCube76YEndpoint')
for name,row in rows.items():
    if sha(ROOT/row['path'])!=row['sha256']:raise RuntimeError(('source changed after scan',name))
project={n for n,r in rows.items() if r['kind']=='project'}
local={n for n,r in rows.items() if r['kind']=='local'}
shared=project&set(base['sources']);new=project-set(base['sources'])
changed={n for n in shared if rows[n]['sha256']!=base['sources'][n]['sha256']}
import_changed={n for n in shared if rows[n]['imports']!=base['sources'][n]['imports']}
dirty=set(new)|set(changed)|set(import_changed)
for n in order:
    if rows[n]['kind']=='project' and any(d in dirty for d in rows[n]['imports']):dirty.add(n)
base_reusable=shared-dirty
project_roots=sorted({d for n in local for d in rows[n]['imports'] if d in project})
project_to_local=sorted((n,d) for n in project for d in rows[n]['imports'] if d in local)
rebuild_order=[n for n in order if n in dirty and n in project]
seen=set(base_reusable)
for n in rebuild_order:
    if any(d in project and d not in seen for d in rows[n]['imports']):raise ValueError(('invalid project rebuild order',n))
    seen.add(n)
if any(d in dirty for n in base_reusable for d in rows[n]['imports']):raise ValueError('reusable base source depends on dirty project source')
new_external=sorted(external-set(base['external_modules'])-{'Init'})
relpaths=[rows[n]['path'] for n in order]
tracked={x.decode() for x in subprocess.check_output(['git','ls-files','-z','--',*relpaths],cwd=ROOT).split(b'\0') if x}
untracked=sorted(set(relpaths)-tracked)
if untracked:raise RuntimeError(('untracked source paths',untracked))
changed_paths={x.decode() for x in subprocess.check_output(['git','diff','--name-only','-z','HEAD','--',*relpaths],cwd=ROOT).split(b'\0') if x}
if changed_paths:raise RuntimeError(('workspace differs from HEAD',sorted(changed_paths)))
result={'status':'SOURCE_PLAN_ONLY','target':'P64QCube76YEndpoint',
        'base_manifest_sha256':BASE_SHA,'local_count':len(local),'project_count':len(project),'external_count':len(external),
        'project_boundary_imports_from_local':project_roots,
        'project_overlap_base':len(shared),'new_project_count':len(new),'changed_overlap_count':len(changed),
        'changed_overlap':sorted(changed),'import_changed_overlap':sorted(import_changed),
        'project_dirty_count':len(dirty),'dirty_overlapping_base_count':len(dirty&shared),'clean_overlap_count':len(base_reusable),
        'local_order':[n for n in order if n in local],'project_order':[n for n in order if n in project],
        'project_rebuild_order':rebuild_order,'project_to_local_edges':project_to_local,
        'new_project_modules':sorted(new),'new_direct_external_modules':new_external,'untracked_source_paths':untracked,
        'sources':rows,'scope':'Point-in-time source-declared graph; no Lean --deps, coherent replay, promotion, byte/file binding or provider ancestry authentication.'}
payload=json.dumps(result,indent=2,sort_keys=True)+'\n'
if sys.argv[1:]==['--write']:
    with OUT.open('x') as f:f.write(payload)
elif sys.argv[1:]:raise SystemExit('usage: python3 -I -S -B survey.py [--write]')
elif not OUT.is_file() or OUT.read_text()!=payload:raise SystemExit('result differs or is absent')
print(json.dumps({k:result[k] for k in ('status','local_count','project_count','project_overlap_base','new_project_count','changed_overlap_count','project_dirty_count','dirty_overlapping_base_count','clean_overlap_count','new_direct_external_modules','untracked_source_paths')},sort_keys=True))

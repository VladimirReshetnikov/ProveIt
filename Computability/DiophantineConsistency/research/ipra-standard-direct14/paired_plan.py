#!/usr/bin/env python3
"""Plan a source-declared extension of a *future* matched AQ29 project pair.

This read-only planner neither authenticates that pair nor compiles Lean.  In
particular, its line-based header scanner is not Lean's parser.  Any actual
replay must independently verify Lean's direct dependencies and all providers.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tomllib

ROOT = Path(__file__).resolve().parents[4]
POLICY_REL = 'Computability/DiophantineConsistency/research/ipra-standard-direct14/historical/task-policy.json'
POLICY_SHA256 = '2b157860dd840d46972bbadfc808cdc570a59abcefb1ca229df685eb17db0273'
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")
_policy_raw=(ROOT/POLICY_REL).read_bytes()
if hashlib.sha256(_policy_raw).hexdigest()!=POLICY_SHA256:raise ValueError('direct14 policy pin mismatch')
TASK = json.loads(_policy_raw)
TARGETS = tuple(TASK['addition_order'])

def draft_map(root):
    return {name: root/row['workspace_path'] for name, row in TASK['sources'].items()
            if row['workspace_path'] != ('Computability/DiophantineConsistency/Lean/' + name.replace('.', '/') + '.lean')}

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def imports(raw):
    """Conservative line scanner, deliberately not a substitute for --deps."""
    s = raw.decode('utf-8'); out=[]; i=0; depth=0
    while i < len(s):
        if depth:
            if s.startswith('/-', i): depth+=1; i+=2
            elif s.startswith('-/', i): depth-=1; i+=2
            else:
                if s[i]=='\n': out.append('\n')
                i+=1
        elif s.startswith('/-', i): depth=1; i+=2
        elif s.startswith('--', i):
            while i<len(s) and s[i]!='\n': i+=1
        else: out.append(s[i]); i+=1
    if depth: raise ValueError('unclosed comment')
    result=[]
    for line in ''.join(out).splitlines():
        m=re.match(r'^\s*(?:(?:public|meta)\s+)*import\s+(.+?)\s*$',line)
        if m:
            names=m.group(1).split()
            if not names or any(not MODULE.fullmatch(name) for name in names):
                raise ValueError(('unsupported import syntax',line))
            result.extend(names)
    return result

def plan(root, snapshot, parent, libs, targets, draft_map, basis, manifest_only=False):
    if basis not in ('historical','current'): raise ValueError('invalid basis')
    if manifest_only and basis!='historical':raise ValueError('manifest-only survey requires historical basis')
    rows={}; order=[]; external=set(); visiting=set(); drift=[]
    sources=parent['sources']; parent_order=parent['order']
    if (parent.get('status')!='FROZEN_NOT_COMPILED' or
            len(set(parent_order))!=len(parent_order) or set(parent_order)!=set(sources) or
            len(parent_order)!=parent['project_modules']):
        raise ValueError('invalid parent source manifest')
    def visit(name):
        if name in rows or name in external:return
        if not MODULE.fullmatch(name):raise ValueError(('invalid module',name))
        if name in visiting:raise ValueError(('import cycle',name))
        top=name.split('.')[0]
        if top not in libs:external.add(name);return
        if manifest_only and name in sources:
            old=sources[name];deps=old['imports']
            visiting.add(name)
            for dep in deps:visit(dep)
            visiting.remove(name)
            rows[name]={'source_kind':'parent_manifest_unchecked',
                        'workspace_path':old['workspace_path'],
                        'source_sha256':old['sha256'],'current_workspace_sha256':None,'imports':deps}
            order.append(name)
            return
        live=libs[top]/(name.replace('.','/')+'.lean')
        if name in draft_map:
            if live.exists():raise ValueError(('draft shadows live source',name))
            live=draft_map[name]
        if not live.is_file() or live.is_symlink():raise ValueError(('missing or symlink source',name,str(live)))
        current=live.read_bytes(); current_sha=sha(current)
        if name in sources:
            old=sources[name]; frozen=snapshot/old['snapshot_path']
            expected=snapshot/'src'/(name.replace('.','/')+'.lean')
            if frozen!=expected or frozen.is_symlink() or not frozen.is_file():
                raise ValueError(('bad parent snapshot path',name))
            saved=frozen.read_bytes()
            if sha(saved)!=old['sha256'] or imports(saved)!=old['imports']:
                raise ValueError(('parent source mismatch',name))
            changed=current_sha!=old['sha256'] or imports(current)!=old['imports']
            if changed:drift.append(name)
            raw=saved if basis=='historical' else current
            source_kind='parent_snapshot'
        else:
            raw=current; source_kind='draft_source' if name in draft_map else 'current_addition'
        deps=imports(raw)
        visiting.add(name)
        for dep in deps:visit(dep)
        visiting.remove(name)
        rows[name]={'source_kind':source_kind,'workspace_path':str(live.relative_to(root)),
                    'source_sha256':sha(raw),'current_workspace_sha256':current_sha,'imports':deps}
        order.append(name)
    for target in targets:visit(target)
    for name,row in rows.items():
        if name not in sources and sha((root/row['workspace_path']).read_bytes())!=row['source_sha256']:
            raise ValueError(('additional source changed during survey',name))
    if basis=='current' and drift:
        raise ValueError(('parent source drift requires coherent successor rebuild',sorted(drift)))
    return {'status':'PROVISIONAL_MANIFEST_PLAN' if manifest_only else 'SOURCE_PLAN_ONLY',
            'basis':basis,'targets':list(targets),
            'parent_source_modules_used':[n for n in order if n in sources],
            'additional_project_modules':[n for n in order if n not in sources],
            'parent_source_drift':None if manifest_only else sorted(drift),'order':order,'sources':rows,
            'external_modules':sorted(external),
            'scope':('Parent source bytes and workspace drift were not checked. ' if manifest_only else '')+
                    'Source-declared candidate closure only; no Lean parsing, build, parent-pair authentication, '
                    'source-to-object provenance, runtime-load trace, or proof validation.'}

def main():
    p=argparse.ArgumentParser();p.add_argument('--snapshot',type=Path,required=True)
    p.add_argument('--parent-sha256',required=True);p.add_argument('--basis',choices=['current','historical'],required=True)
    p.add_argument('--manifest-only',action='store_true',help='low-I/O provisional graph survey; does not check parent source bytes or drift')
    p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    snapshot=a.snapshot.resolve(strict=True); parent_raw=(snapshot/'manifest.json').read_bytes()
    if sha(parent_raw)!=a.parent_sha256:raise ValueError('parent manifest pin mismatch')
    parent=json.loads(parent_raw)
    if Path(parent['root']).resolve()!=ROOT.resolve():raise ValueError('different parent workspace')
    for path,key in ((ROOT/'lakefile.toml','lakefile_sha256'),(ROOT/'lean-toolchain','lean_toolchain_sha256')):
        if sha(path.read_bytes())!=parent[key]:raise ValueError(('parent configuration drift',str(path)))
    cfg=tomllib.loads((ROOT/'lakefile.toml').read_text())
    libs={x['name']:ROOT/x.get('srcDir','.') for x in cfg['lean_lib']};libs.pop('Foundation',None)
    drafts=draft_map(ROOT)
    result=plan(ROOT,snapshot,parent,libs,TARGETS,drafts,a.basis,a.manifest_only)
    paths=[result['sources'][n]['workspace_path'] for n in result['additional_project_modules']]
    tracked=subprocess.check_output(['git','ls-files','-z','--',*paths],cwd=ROOT).split(b'\0')
    modified=subprocess.check_output(['git','diff','--name-only','-z','HEAD','--',*paths],cwd=ROOT).split(b'\0')
    result['additional_untracked']=sorted(set(paths)-{p.decode() for p in tracked if p})
    result['additional_modified_against_head']=sorted(p.decode() for p in modified if p)
    result.update({'parent_manifest_sha256':a.parent_sha256,'parent_snapshot':str(snapshot),
                   'planner_sha256':sha(Path(__file__).read_bytes()),
                   'workspace_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()})
    if result['additional_project_modules'] != list(TARGETS):raise ValueError('direct14 additions differ from pinned order')
    for name in TARGETS:
        row=result['sources'][name]; expected=TASK['sources'][name]
        if (row['source_sha256'],row['workspace_path'],row['imports']) != (expected['sha256'],expected['workspace_path'],expected['imports']):
            raise ValueError(('direct14 source differs from task policy',name))
    if a.output.exists() or a.output.is_symlink():raise ValueError('refusing to overwrite plan')
    with a.output.open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
    drift='unchecked' if result['parent_source_drift'] is None else str(len(result['parent_source_drift']))
    print(result['status'],len(result['parent_source_modules_used']),'parent modules',
          len(result['additional_project_modules']),'additional modules; drift',drift,flush=True)

if __name__=='__main__':main()

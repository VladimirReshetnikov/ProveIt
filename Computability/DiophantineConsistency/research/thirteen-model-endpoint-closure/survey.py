#!/usr/bin/env python3
"""Source-declared incremental closure survey; it does not compile Lean."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tomllib

if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):
    raise RuntimeError('closure survey rejects optimized Python')
HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1]
ROOT=BASE.parents[1]
PARENT=Path('/tmp/ipra-ordinary12-coexistence-source-03')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
TOOLCHAIN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
MANIFEST=HERE/'source-manifest.json'
PARENT_HASH='9a7059e439bb77ab258808789fd1165cff8a4961c609e132ca0ed2130cb27ded'
ROOTS=['DiophantineConsistency.ModelThirteenCarrier']
NAME=re.compile(r'^[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*$')
H=lambda b:hashlib.sha256(b).hexdigest()


def git(*args):
    p=subprocess.run(['git',*args],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    if p.returncode:raise ValueError(('git failed',args,p.returncode,p.stderr.decode(errors='replace')))
    return p.stdout


def strip_comments(text,path):
    out=[];i=0;depth=0;quoted=False
    while i<len(text):
        c=text[i];n=text[i:i+2]
        if depth:
            if n=='/-':depth+=1;out.extend('  ');i+=2
            elif n=='-/':depth-=1;out.extend('  ');i+=2
            else:out.append('\n' if c=='\n' else ' ');i+=1
        elif quoted:
            out.append(c);i+=1
            if c=='\\' and i<len(text):out.append(text[i]);i+=1
            elif c=='"':quoted=False
        elif n=='/-':depth=1;out.extend('  ');i+=2
        elif n=='--':
            while i<len(text) and text[i]!='\n':out.append(' ');i+=1
        else:
            out.append(c);i+=1
            if c=='"':quoted=True
    if depth or quoted:raise ValueError(('unterminated comment or string',str(path)))
    return ''.join(out)


def imports(raw,path):
    result=[]
    for number,line in enumerate(strip_comments(raw.decode('utf-8'),path).splitlines(),1):
        if line.startswith('import '):
            names=line.split()[1:]
            if not names or any(not NAME.fullmatch(n) for n in names):
                raise ValueError(('unexpected import line',str(path),number,line))
            result.extend(names)
        elif line.lstrip().startswith('import '):
            raise ValueError(('indented import needs manual handling',str(path),number))
    return result


def build(anchor):
    git('merge-base','--is-ancestor',anchor,'HEAD')
    lake=(ROOT/'lakefile.toml').read_bytes()
    if lake!=git('show',f'{anchor}:lakefile.toml'):raise ValueError('lakefile differs from anchor')
    toolchain=(ROOT/'lean-toolchain').read_bytes()
    if toolchain!=git('show',f'{anchor}:lean-toolchain'):raise ValueError('toolchain differs from anchor')
    libraries={}
    for lib in tomllib.loads(lake.decode('utf-8')).get('lean_lib',[]):
        name=lib['name']; source=lib.get('srcDir','.')
        if name in libraries and libraries[name]!=source:raise ValueError(('duplicate lake library',name))
        libraries[name]=source
    pm=PARENT/'manifest.json'
    if H(pm.read_bytes())!=PARENT_HASH:raise ValueError('parent manifest drift')
    frozen=json.loads(pm.read_text())
    if frozen['status']!='FROZEN_NOT_COMPILED':raise ValueError(('bad parent status',frozen['status']))
    boundaries=frozen['sources']
    if len(boundaries)!=70 or set(boundaries)!=set(frozen['order']):
        raise ValueError('unexpected frozen parent membership')
    for name,row in boundaries.items():
        workspace=ROOT/row['workspace_path']; snap=PARENT/row['snapshot_path']
        if H(workspace.read_bytes())!=row['sha256'] or H(snap.read_bytes())!=row['sha256']:
            raise ValueError(('frozen parent source drift',name))
        if H(git('show',f"{anchor}:{row['workspace_path']}"))!=row['sha256']:
            raise ValueError(('frozen parent differs from pinned commit',name))
    visited={};active=set();order=[];used_parent=set();external=set()
    def visit(name):
        if name in boundaries:
            used_parent.add(name);return
        if name in visited:return
        if name in active:raise ValueError(('source import cycle',name))
        top=name.split('.')[0]
        # Foundation is supplied by the audited package provider, not by
        # this workspace's unavailable local Foundation source tree.
        if top == 'Foundation':
            external.add(name);return
        if top not in libraries:
            external.add(name);return
        prefix=ROOT/libraries[top]
        path=prefix/Path(*name.split('.')).with_suffix('.lean')
        if not path.is_file():raise ValueError(('missing project source',name,str(path)))
        rel=path.relative_to(ROOT).as_posix()
        current=path.read_bytes(); historical=git('show',f'{anchor}:{rel}')
        if current!=historical:raise ValueError(('workspace differs from pinned commit',name,rel))
        deps=imports(current,path)
        active.add(name)
        for dep in deps:visit(dep)
        active.remove(name)
        visited[name]={'workspace_path':rel,'sha256':H(current),'imports':deps}
        order.append(name)
    for root in ROOTS:visit(root)
    externals={}
    for name in sorted(external):
        path=PACKAGE/Path(*name.split('.')).with_suffix('.olean')
        if not path.is_file():path=TOOLCHAIN/Path(*name.split('.')).with_suffix('.olean')
        externals[name]={'path':str(path),'sha256':H(path.read_bytes()) if path.is_file() else None}
    return {'status':'SOURCE_DECLARED_INCREMENTAL_CLOSURE_SURVEY','source_anchor':anchor,
            'parent_manifest':str(pm),'parent_manifest_sha256':PARENT_HASH,
            'lakefile_sha256':H(lake),'lean_toolchain_sha256':H(toolchain),
            'parent_source_count':len(boundaries),'roots':ROOTS,'order':order,
            'additional_project_modules':len(order),'direct_parent_boundary':sorted(used_parent),
            'sources':visited,'external_direct':externals,
            'scope':'Source-declared endpoint closure survey only; no Lean run, no axiom inventory, no dynamic/package-transitive import audit, no DAG binding, no fixed-port calibration, and no iPRA proof.'}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--write',action='store_true');args=ap.parse_args()
    if args.write:
        if MANIFEST.exists() or MANIFEST.is_symlink():raise ValueError('refusing manifest overwrite')
        anchor=git('rev-parse','HEAD').decode().strip()
    else:
        anchor=json.loads(MANIFEST.read_text())['source_anchor']
    result=build(anchor)
    missing=[n for n,row in result['external_direct'].items() if row['sha256'] is None]
    if missing:raise ValueError(('unresolved direct external imports',missing))
    if args.write:
        with MANIFEST.open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
    elif result!=json.loads(MANIFEST.read_text()):raise ValueError('manifest mismatch')
    print('PASS_SOURCE_DECLARED_CLOSURE',result['additional_project_modules'],
          'parent-boundary',len(result['direct_parent_boundary']),'missing-external',missing)

if __name__=='__main__':main()

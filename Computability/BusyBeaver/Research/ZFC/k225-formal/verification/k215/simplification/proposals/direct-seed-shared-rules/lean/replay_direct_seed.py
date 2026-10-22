#!/usr/bin/env python3
"""Clean serial replay of the direct-seed and retained legacy Lean API clients.

Usage:
  python3 replay_direct_seed.py --repo /path/to/ProveIt --lean /path/to/lean

Requires Python 3.11+ and Lean 4.32.0. Does not modify the repository.
An existing nonempty output directory is rejected; choose a new --output.
All project modules are compiled from source; only Lean's shipped standard
library objects are outside this replay. No Lake or project cache is used.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import tomllib

PIN = "6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95"
TARGETS = ["BusyBeaver.ZFC.AuditSeedDirect222", "BusyBeaver.ZFC.AuditSeedLegacy222"]
HERE = Path(__file__).resolve().parent

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def imports(text):
    # These input files use ordinary module imports, one or several per line.
    # Remove nested Lean block comments before scanning declarations.
    output=[]; depth=0; i=0
    while i<len(text):
        pair=text[i:i+2]
        if pair=="/-": depth+=1; i+=2; continue
        if pair=="-/" and depth: depth-=1; i+=2; continue
        if depth:
            if text[i]=='\n': output.append('\n')
            i+=1; continue
        if pair=='--':
            while i<len(text) and text[i]!='\n': i+=1
            continue
        output.append(text[i]); i+=1
    result=[]
    for names in re.findall(r"^\s*(?:public\s+)?import\s+([^\n]+)", ''.join(output), re.M):
        for name in names.split():
            if not re.fullmatch(r'[A-Za-z0-9_.]+',name):
                raise ValueError(f'Unsupported import syntax: {name!r}')
            result.append(name)
    return result

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo',type=Path,required=True)
    parser.add_argument('--lean',type=Path,required=True)
    parser.add_argument('--overlay',type=Path,default=HERE/'overlay')
    parser.add_argument('--output',type=Path,default=HERE/'fresh-replay')
    parser.add_argument('--manifest',type=Path,default=HERE/'source-manifest.json')
    args=parser.parse_args()
    repo=args.repo.resolve(); lean=args.lean.resolve(); overlay=args.overlay.resolve()
    out=args.output.resolve()
    if out.exists() and any(out.iterdir()):
        parser.error('Output directory must be new or empty; no project cache is reused.')
    out.mkdir(parents=True,exist_ok=True)
    build=out/'build'; logs=out/'logs'
    build.mkdir(); logs.mkdir()
    version=subprocess.run([str(lean),'--version'],capture_output=True,text=True,check=True).stdout.strip()
    if not re.search(r'version 4\.32\.0(?:,|\s)',version):
        parser.error(f'Expected Lean 4.32.0, got {version}')
    commit=subprocess.run(['git','rev-parse','HEAD'],cwd=repo,capture_output=True,text=True,check=True).stdout.strip()
    if commit != PIN:
        parser.error(f'Expected repository revision {PIN}; got {commit}')
    config=tomllib.loads((repo/'lakefile.toml').read_text())
    roots=[overlay,repo]+[repo/x.get('srcDir','.') for x in config.get('lean_lib',[])]
    seen=set(); active=set(); order=[]; data={}
    def visit(name):
        if name in active: raise RuntimeError(f'Import cycle: {name}')
        if name in seen: return
        rel=Path(name.replace('.','/')+'.lean')
        matches=[(r,r/rel) for r in roots if (r/rel).is_file()]
        if not matches:
            if name.split('.')[0] in {'Init','Lean','Std'}: return
            raise FileNotFoundError(name)
        srcroot,path=matches[0]
        deps=imports(path.read_text())
        data[name]={'module':name,'source_kind':'overlay' if srcroot==overlay else 'repository',
                    'source_path':str(path.relative_to(overlay if srcroot==overlay else repo)),
                    'sha256':sha(path),'imports':deps}
        active.add(name)
        for dep in deps: visit(dep)
        active.remove(name); seen.add(name); order.append((name,srcroot,path,rel))
    for target in TARGETS: visit(target)
    manifest={'repository_revision':PIN,'targets':TARGETS,'sources':[data[n] for n,_,_,_ in order]}
    if args.manifest.exists():
        expected=json.loads(args.manifest.read_text())
        if manifest!=expected:
            raise RuntimeError('Resolved source bytes/imports differ from the delivered source manifest.')
    (out/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    env={**os.environ,'LEAN_PATH':str(build)}
    records=[]; start=time.monotonic()
    with (out/'events.jsonl').open('w') as events:
        for name,srcroot,path,rel in order:
            obj=build/rel.with_suffix('.olean'); obj.parent.mkdir(parents=True,exist_ok=True)
            command=[str(lean),'-o',str(obj),str(rel)]
            t=time.monotonic()
            run=subprocess.run(command,cwd=srcroot,env=env,capture_output=True,text=True)
            text=run.stdout+run.stderr
            log=logs/(name+'.log'); log.write_text(text)
            row={**data[name],'status':run.returncode,'seconds':round(time.monotonic()-t,6),
                 'command':command,'cwd':str(srcroot),'log_sha256':sha(log),
                 'object_sha256':sha(obj) if obj.exists() else None,
                 'warning_count':len(re.findall(r'\bwarning:',text))}
            records.append(row); events.write(json.dumps(row)+'\n'); events.flush()
            print(f'{len(records)}/{len(order)} {name}: {run.returncode}',flush=True)
            if run.returncode or 'sorryAx' in text:
                print(text); raise RuntimeError(f'Compilation or axiom check failed: {name}')
    expected_counts={TARGETS[0]:9,TARGETS[1]:2}
    reports={}
    standard={'propext','Classical.choice','Quot.sound'}
    for target,count in expected_counts.items():
        text=(logs/(target+'.log')).read_text()
        found=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text,re.S)
        if len(found)!=count: raise RuntimeError(f'Missing axiom reports for {target}')
        for name,body in found:
            axioms={x.strip() for x in body.split(',') if x.strip()}
            expected=standard-{'Classical.choice'} if name.endswith(('free_lt_enc','free_th')) else standard
            if axioms != expected: raise RuntimeError(f'Unexpected axioms for {name}: {axioms}')
            reports[name]=sorted(axioms)
    summary={'repository_revision':PIN,'lean_version':version,'compiler_sha256':sha(lean),
             'targets':TARGETS,'project_modules_compiled':len(records),'project_cache_reuse':0,
             'elapsed_seconds':round(time.monotonic()-start,6),
             'warning_count':sum(x['warning_count'] for x in records),
             'audit_client_warning_count':sum(x['warning_count'] for x in records if x['module'] in TARGETS),
             'axiom_reports':reports,'records':records,
             'scope':'Generic endpoint and direct/legacy seed APIs; no machine-specific K215 certificates replayed.'}
    (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({k:v for k,v in summary.items() if k!='records'},indent=2))

if __name__=='__main__':
    main()

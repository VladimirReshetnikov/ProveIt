#!/usr/bin/env python3
"""Build the bundled Lean source closure, with no external ProveIt checkout.

Requires Lean 4.32.0. A supplied --lean path avoids dependence on elan.
All dependencies are rebuilt from .lean sources in a separate build directory.
"""
from pathlib import Path
import argparse, hashlib, json, os, re, shutil, subprocess, time

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean',default=os.environ.get('LEAN_BIN','lean'))
    p.add_argument('--build-dir',type=Path)
    a=p.parse_args()
    here=Path(__file__).resolve().parent
    src=here/'src'
    build=(a.build_dir or here/'build').resolve()
    build.mkdir(parents=True,exist_ok=True)
    lean=shutil.which(a.lean)
    if lean is None: raise SystemExit('Lean executable not found; pass --lean /path/to/lean')
    version=subprocess.check_output([lean,'--version'],text=True).strip()
    if 'version 4.32.0,' not in version:
        raise SystemExit('This source bundle was verified with Lean 4.32.0; found '+version)
    manifest=json.loads((here.parent/'source_manifest.json').read_text())
    for e in manifest['sources']:
        if e['bundle_path'].startswith('formal/src/'):
            path=here.parent/e['bundle_path']
            if hashlib.sha256(path.read_bytes()).hexdigest()!=e['sha256']:
                raise SystemExit('Pinned source hash mismatch: '+e['bundle_path'])
    order=[];seen=set()
    def visit(module):
        if module in seen:return
        seen.add(module)
        rel=Path(*module.split('.')).with_suffix('.lean')
        f=src/rel
        if not f.exists():
            if module.split('.')[0] in ('Init','Lean','Std'):return
            raise FileNotFoundError(module)
        for m in re.finditer(r'^import\s+([^\n]+)',f.read_text(),re.M):
            for dep in m[1].split('--')[0].split():visit(dep)
        order.append((module,rel))
    visit('BusyBeaver.ZFC.CheckTheory254')
    env=dict(os.environ,LEAN_PATH=str(build))
    audit={'lean_version':version,'scope':'Fresh source build of the bundled literal-DAG and abstract-enumerator theorems; no binary/ZFC endpoint asserted.',
           'modules':[]}
    print(version,flush=True)
    for module,rel in order:
        out=build/rel.with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
        started=time.monotonic()
        command=[lean,'-o',str(out),str(rel)]
        r=subprocess.run(command,cwd=src,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        out.with_suffix('.log').write_text(r.stdout)
        entry={'module':module,'source':str(Path('formal/src')/rel),
               'sha256':hashlib.sha256((src/rel).read_bytes()).hexdigest(),
               'command':command,'returncode':r.returncode,'seconds':round(time.monotonic()-started,3),
               'log':str(rel.with_suffix('.log'))}
        audit['modules'].append(entry)
        (build/'build_audit.json').write_text(json.dumps(audit,indent=2)+'\n')
        print(f'{module}: exit {r.returncode}',flush=True)
        if r.returncode or 'sorryAx' in r.stdout or "declaration uses 'sorry'" in r.stdout:
            print(r.stdout,flush=True);raise SystemExit(1)
    log=(build/'BusyBeaver/ZFC/CheckTheory254.log').read_text()
    if log.count('depends on axioms:')!=9:
        raise SystemExit('Expected nine exact theorem axiom reports')
    audit['status']='PASS';audit['axiom_audit_reports']=9
    (build/'build_audit.json').write_text(json.dumps(audit,indent=2)+'\n')
    print(f'PASS: {len(order)} modules compiled from source; 9 theorem audits. Output: {build}',flush=True)

if __name__=='__main__':main()

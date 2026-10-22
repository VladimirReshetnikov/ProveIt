#!/usr/bin/env python3
"""Check all delivered Lean replacements together; measure the endpoint import cut.

This compiles the union of affected local dependency closures and four typed
clients. It deliberately does not claim a complete KEndpoint215 rebuild.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time
import tomllib

PIN = '57541fe0cfe3af62b4cb58747d8d1d7c16b338d5'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, required=True)
    ap.add_argument('--lean', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    repo, lean, out = args.repo.resolve(), args.lean.resolve(), args.out.resolve()
    package = Path(__file__).resolve().parents[1]
    if out.exists():
        raise SystemExit('Output directory must not exist; builds must be fresh.')
    if subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip() != PIN:
        raise SystemExit('Wrong baseline revision.')
    if subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=repo,text=True):
        raise SystemExit('Use a pristine baseline checkout.')
    version = subprocess.check_output([str(lean),'--version'],text=True).strip()
    if '4.32.0' not in version:
        raise SystemExit('Lean 4.32.0 is required.')
    config = tomllib.loads((repo/'lakefile.toml').read_text())
    roots = list(dict.fromkeys(repo/s.get('srcDir','.') for s in config['lean_lib']))
    overlays = [package/'lean_logic/refactor', package/'dense_bridge', package/'semantic_interface/refactor']
    cache = {}
    def source(m, changed):
        key = m, changed
        if key in cache:
            return cache[key]
        rel = Path(m.replace('.','/')+'.lean')
        candidates = ([x/rel for x in overlays] if changed else [])+[x/rel for x in roots]
        path = next((p for p in candidates if p.is_file()), None)
        if path is None:
            if m.split('.')[0] not in {'Init','Std','Lean'}:
                raise ValueError('Missing local project module: '+m)
            cache[key] = None
            return None
        data = path.read_bytes()
        deps = []
        for line in data.decode().splitlines():
            if line.startswith('import '):
                deps.extend(line[7:].split('--')[0].split())
        cache[key] = path, data, deps
        return cache[key]
    def closure(targets, changed):
        seen, active, order = set(), set(), []
        def visit(m):
            if m in seen:
                return
            if m in active:
                raise ValueError('Import cycle: '+m)
            s = source(m, changed)
            if s is None:
                seen.add(m)
                return
            active.add(m)
            for dep in s[2]:
                visit(dep)
            active.remove(m)
            seen.add(m)
            order.append(m)
        for t in targets:
            visit(t)
        return order
    endpoint = 'BusyBeaver.ZFC.KEndpoint215'
    old, new = closure([endpoint],False), closure([endpoint],True)
    targets = ['BusyBeaver.ZFC.KCodeDom','BusyBeaver.ZFC.KThmK','BusyBeaver.ZFC.Numeric254',
               'BusyBeaver.ZFC.TarskiFalsity','BusyBeaver.ZFC.KDenseBridge',
               'BusyBeaver.ZFC.WFModelCore','BusyBeaver.ZFC.PSCCalibration']
    order = closure(targets,True)
    out.mkdir(parents=True)
    work, logs = out/'sources', out/'logs'
    work.mkdir(); logs.mkdir()
    records=[]
    for m in order:
        _, data, deps = source(m,True)
        target=work/(m.replace('.','/')+'.lean')
        target.parent.mkdir(parents=True,exist_ok=True)
        target.write_bytes(data)
    audits={'LogicAudit':package/'lean_logic/CommonAudit.lean',
            'ExtendedLogicAudit':package/'lean_logic/ExtendedAudit.lean',
            'DenseAudit':package/'dense_bridge/Audit.lean',
            'PowerSetsAudit':package/'semantic_interface/Audit.lean'}
    for m, path in audits.items():
        (work/(m+'.lean')).write_bytes(path.read_bytes())
    env=dict(os.environ,LEAN_PATH=str(work))
    for m in order+list(audits):
        rel=m.replace('.','/')
        started=time.monotonic()
        p=subprocess.run([str(lean),'-o',rel+'.olean',rel+'.lean'],cwd=work,env=env,
                         stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=300)
        elapsed=time.monotonic()-started
        (logs/(m+'.log')).write_text(p.stdout)
        records.append({'module':m,'returncode':p.returncode,'seconds':round(elapsed,3),
                        'source_sha256':sha((work/(rel+'.lean')).read_bytes())})
        print(m,p.returncode,round(elapsed,3),flush=True)
        if p.returncode:
            print(p.stdout,flush=True)
            (out/'failed.json').write_text(json.dumps(records,indent=2))
            raise SystemExit(p.returncode)
    comparisons={
        'logic_audit': (logs/'LogicAudit.log').read_bytes() == (package/'lean_logic/evidence/baseline/CommonAudit.log').read_bytes(),
        'extended_axiom_free': (logs/'ExtendedLogicAudit.log').read_text().count('does not depend on any axioms') == 3,
        'powersets_audit': (logs/'PowerSetsAudit.log').read_bytes() == (package/'semantic_interface/verification/audit.log').read_bytes(),
    }
    if not all(comparisons.values()):
        raise SystemExit('An exact audit comparison failed: '+str(comparisons))
    result={'baseline_commit':PIN,'lean_version':version,'scope':'Combined focused Lean closure; endpoint import census only.',
            'endpoint_recompiled':False,'fresh_project_modules':len(order),'typed_audits':len(audits),
            'comparisons':comparisons,'records':records,
            'endpoint_census':{'before_modules':len(old),'after_modules':len(new),
                               'before_bytes':sum(len(source(m,False)[1]) for m in old),
                               'after_bytes':sum(len(source(m,True)[1]) for m in new),
                               'removed':sorted(set(old)-set(new)),'added':sorted(set(new)-set(old))}}
    (out/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['fresh_project_modules','typed_audits','comparisons','endpoint_census']},indent=2))

if __name__ == '__main__':
    main()

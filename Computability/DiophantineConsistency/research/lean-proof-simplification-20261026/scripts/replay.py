#!/usr/bin/env python3
"""Replay checked demonstrations against the pinned ProveIt checkout.

No candidate patches are applied. Default selection comes from validation.json.
Pass --include-proposals to try unvalidated demonstration files as well.
"""
import argparse
import json
import re
import subprocess
import time
from pathlib import Path

PIN = '60e9c5d620c6c387d932876cfa2d9376f64ea56c'

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('repo', type=Path)
    ap.add_argument('--without-build', action='store_true', help='Reuse existing dependency oleans.')
    ap.add_argument('--include-proposals', action='store_true')
    ap.add_argument('--output', type=Path, default=Path('replay-output'))
    args = ap.parse_args()
    repo=args.repo.resolve(); bundle=Path(__file__).resolve().parents[1]
    got=subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()
    if got != PIN:
        raise SystemExit(f'Expected commit {PIN}; found {got}. Use an isolated pinned checkout.')
    if (repo/'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.32.0':
        raise SystemExit('The pinned Lean toolchain is required.')
    args.output=args.output.resolve(); args.output.mkdir(parents=True,exist_ok=True)
    evidence=json.loads((bundle/'validation/validation.json').read_text())
    entries=[x for x in evidence['demonstrations'] if x['status']=='compiled' or args.include_proposals]
    sources=[bundle/x['path'] for x in entries]
    imports=set()
    for p in sources:
        if not p.is_file(): raise SystemExit(f'Missing packaged source: {p}')
        for line in re.findall(r'^import\s+([^\n]+)',p.read_text(),re.M):
            imports.update(n for n in line.split() if n.startswith(('DiophantineConsistency.','Diophantine.')))
    if imports and not args.without_build:
        with (args.output/'dependencies.log').open('w') as f:
            rc=subprocess.run(['lake','build',*sorted(imports)],cwd=repo,stdout=f,stderr=subprocess.STDOUT).returncode
        if rc: raise SystemExit(f'Dependency build failed; see {args.output}/dependencies.log')
    results=[]
    for entry,p in zip(entries,sources):
        log=args.output/(p.stem+'.log'); start=time.monotonic()
        with log.open('w') as f:
            rc=subprocess.run(['lake','env','lean','-j1',str(p)],cwd=repo,stdout=f,stderr=subprocess.STDOUT).returncode
        text=log.read_text(errors='replace')
        forbidden=[s for s in ['sorryAx','Lean.ofReduceBool','Lean.ofReduceNat','Lean.trustCompiler','._native.'] if s in text]
        result=dict(path=entry['path'],exit_code=rc,forbidden_axiom_markers=forbidden,
                    elapsed_seconds=round(time.monotonic()-start,3),log=str(log))
        results.append(result); print(json.dumps(result),flush=True)
    (args.output/'results.json').write_text(json.dumps(results,indent=2)+'\n')
    if any(r['exit_code'] or r['forbidden_axiom_markers'] for r in results):
        raise SystemExit(1)

if __name__=='__main__': main()

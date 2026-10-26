#!/usr/bin/env python3
"""Replay exactly the checks claimed in the report; never edits a project.

Use --project PATH for a configured checkout with the pinned Lean/mathlib.
Advanced use: --compiler PATH --lean-path PATHS to supply the same environment.
This does NOT validate the internal-model source patches or full NativePellBootstrap.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--project', type=Path)
p.add_argument('--compiler', type=Path)
p.add_argument('--lean-path')
p.add_argument('--out', type=Path, required=True)
a = p.parse_args()
root = Path(__file__).resolve().parent.parent
out = a.out.resolve()
out.mkdir(parents=True, exist_ok=True)
env = os.environ.copy()
if a.compiler:
    compiler = str(a.compiler.resolve())
    if a.lean_path is not None:
        env['LEAN_PATH'] = a.lean_path
else:
    if a.project is None:
        p.error('Provide --project or --compiler.')
    probe = 'import os,json,shutil;print(json.dumps({"lean":shutil.which("lean"),"LEAN_PATH":os.environ.get("LEAN_PATH",""),"PATH":os.environ.get("PATH","")}))'
    found = json.loads(subprocess.check_output(
        ['lake','env',sys.executable,'-c',probe], cwd=a.project.resolve(), text=True))
    compiler = found['lean']
    env.update({k: found[k] for k in ['LEAN_PATH','PATH']})
version = subprocess.check_output([compiler,'--version'],env=env,text=True).strip()
if 'version 4.32.0' not in version:
    raise SystemExit('This replay requires Lean 4.32.0; observed '+version)
records = []

def run(label, rel, module=None, family=None):
    src = root / rel
    check_env = env.copy()
    cmd = [compiler]
    if family:
        build = out / family
        build.mkdir(exist_ok=True)
        check_env['LEAN_PATH'] = str(build) + os.pathsep + env.get('LEAN_PATH','')
        if module:
            obj = build / (module.replace('.', '/') + '.olean')
            obj.parent.mkdir(parents=True, exist_ok=True)
            cmd += ['-o', str(obj)]
    cmd.append(str(src))
    source_root = src.parents[len(module.split(".")) - 1] if module else src.parent
    result = subprocess.run(cmd,cwd=source_root,env=check_env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log = result.stdout
    (out/(label+'.log')).write_text(log,encoding='utf-8')
    ok = result.returncode == 0 and 'sorryAx' not in log and 'declaration uses `sorry`' not in log
    records.append({'check':label,'source':rel,'sha256':hashlib.sha256(src.read_bytes()).hexdigest(),
        'returncode':result.returncode,'passed':ok,'log':label+'.log'})
    print(('PASS ' if ok else 'FAIL ')+label,flush=True)
    if not ok:
        (out/'results.json').write_text(json.dumps({'compiler':version,'checks':records},indent=2)+'\n')
        raise SystemExit(1)

run('internal-semantic-core','internal/InternalZeroCore.lean')
run('certificate-closure','closure/CertificateClosure.lean')
run('pell-standalone','pell/PellTracePrototype.lean')
run('minima-standalone','minima/MinimaSaturation.lean')
run('discriminant-standalone','minima/QuadraticUnitObstruction.lean')
run('pell-unit-module','pell/patch_sources/DiophantineConsistency/ConsecutivePellUnit.lean',
    'DiophantineConsistency.ConsecutivePellUnit','pell-build')
run('pell-replacement-module','pell/patch_sources/DiophantineConsistency/ConsecutivePell.lean',
    'DiophantineConsistency.ConsecutivePell','pell-build')
run('pell-axioms','pell/PellRefactorChecks.lean',family='pell-build')
run('original-short-equation','minima/replay/DiophantineConsistency/ShortEquation.lean',
    'DiophantineConsistency.ShortEquation','minima-build')
run('original-consecutive-pell','minima/replay/DiophantineConsistency/ConsecutivePell.lean',
    'DiophantineConsistency.ConsecutivePell','minima-build')
run('actual-obstruction-adapters','minima/replay/ExistingObstructionReuse.lean',family='minima-build')
run('full-modified-minimum-norm','minima/replay/DiophantineConsistency/MinimumNorm.lean',
    'DiophantineConsistency.MinimumNorm','minima-build')
run('minimum-norm-endpoint-axioms','minima/replay/AuditMinimumNorm.lean',family='minima-build')
(out/'results.json').write_text(json.dumps({'compiler':version,
    'mathlib_required_commit':'81a5d257c8e410db227a6665ed08f64fea08e997',
    'scope':'Only listed checks; no full project, full ShortSystem, native-bootstrap, or internal-model source patch build.',
    'checks':records},indent=2)+'\n')

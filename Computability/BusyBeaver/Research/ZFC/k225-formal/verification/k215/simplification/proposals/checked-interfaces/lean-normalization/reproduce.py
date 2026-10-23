#!/usr/bin/env python3
"""Freshly check the detached normalization-first ConstructibleAbs pilot.

Requires Python 3.11+, Lean 4.32.0, and a checkout matching sources.json.
Writes only to a new --out directory; never modifies the supplied repository.
Compiles 21 dependencies once, then the baseline and proposed target separately.
This is a local module/API audit, not a K215 endpoint rebuild.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

p = argparse.ArgumentParser()
p.add_argument('--repo', type=Path, required=True)
p.add_argument('--lean', type=Path, required=True)
p.add_argument('--out', type=Path, required=True)
a = p.parse_args()
here = Path(__file__).resolve().parent
repo, lean, out = a.repo.resolve(), a.lean.resolve(), a.out.resolve()
manifest = json.loads((here/'sources.json').read_text())
version = subprocess.check_output([str(lean), '--version'], text=True).strip()
if 'version 4.32.0' not in version:
    raise SystemExit('This replay requires Lean 4.32.0; observed: '+version)
for row in manifest['sources']:
    source = (repo/row['source']).resolve()
    if not source.is_relative_to(repo) or sha(source) != row['sha256']:
        raise SystemExit('Baseline source mismatch: '+row['source'])
proposed = here/'proposed/BusyBeaver/ZFC/ConstructibleAbs.lean'
if sha(proposed) != manifest['proposed_sha256']:
    raise SystemExit('Proposed source does not match the recorded digest')
if out.exists():
    raise SystemExit('--out must name a new directory; previous evidence is never overwritten')
out.mkdir(parents=True)
objects = out/'objects'
objects.mkdir()
env = dict(os.environ, LEAN_PATH=str(objects))
records = []

def compile_file(name, source, source_root, dest=None):
    cmd = [str(lean)]
    if dest is not None:
        dest.parent.mkdir(parents=True, exist_ok=True)
        cmd += ['-o', str(dest)]
    cmd += [str(source.relative_to(source_root))]
    started = time.monotonic()
    proc = subprocess.run(cmd, cwd=source_root, env=env, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = out/(name+'.log')
    log.write_text(proc.stdout)
    row = {'name':name,'source_sha256':sha(source),'returncode':proc.returncode,
           'seconds':time.monotonic()-started,'log':log.name,'log_sha256':sha(log)}
    if dest is not None and proc.returncode == 0:
        row['object_sha256'] = sha(dest)
    records.append(row)
    (out/'records.json').write_text(json.dumps(records, indent=2)+'\n')
    print(name, proc.returncode, f"{row['seconds']:.3f}s", flush=True)
    if proc.returncode:
        print(proc.stdout, flush=True)
        raise SystemExit(proc.returncode)
    return proc.stdout

for row in manifest['sources'][:-1]:
    compile_file(row['module'], repo/row['source'], repo/row['root'],
                 objects/(row['module'].replace('.','/')+'.olean'))
target = manifest['sources'][-1]
assert target['module'] == manifest['module']
target_object = objects/(target['module'].replace('.','/')+'.olean')
compile_file('baseline-module', repo/target['source'], repo/target['root'], target_object)
baseline = compile_file('baseline-api', here/'Audit.lean', here)
compile_file('proposed-module', proposed, here/'proposed', target_object)
changed = compile_file('proposed-api', here/'Audit.lean', here)
if baseline != changed:
    raise SystemExit('The checked public type/axiom reports differ; inspect both API logs')
if 'sorryAx' in changed or 'warning:' in changed or 'error:' in changed:
    raise SystemExit('The proposed API log has a disallowed proof placeholder or diagnostic')
for row in manifest['sources']:
    if sha(repo/row['source']) != row['sha256']:
        raise SystemExit('A baseline source changed during the replay: '+row['source'])
result = {'status':'PASS','scope':'21 dependency modules; baseline and modified ConstructibleAbs; six exact public type/axiom reports',
          'full_endpoint_rebuilt':False,'lean_version':version,
          'baseline_commit':manifest['commit'],'source_manifest_sha256':sha(here/'sources.json'),
          'audit_source_sha256':sha(here/'Audit.lean'),'same_api_output':True,
          'metrics':json.loads((here/'metrics.json').read_text()),'records':records}
(out/'result.json').write_text(json.dumps(result, indent=2)+'\n')
print('PASS: exact public types and axiom profiles agree; full endpoints were not rebuilt.', flush=True)

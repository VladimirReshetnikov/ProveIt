#!/usr/bin/env python3
"""Check the shipped examples and every selected specification's axioms.

Run validate.py first. This reuses its verified production overlay without
changing the checkout or installed dependencies. No network access is used.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import time
from validate import BUNDLE, PIN, head, sha

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', required=True, type=Path)
    ap.add_argument('--lean', required=True, type=Path)
    ap.add_argument('--packages', type=Path)
    ap.add_argument('--validated', required=True, type=Path)
    ap.add_argument('--baseline', type=Path, help='Optional exact-pin original build for before/after specification axiom comparison')
    args = ap.parse_args()
    repo, lean, val = args.repo.resolve(), args.lean.resolve(), args.validated.resolve()
    packages = (args.packages or repo/'.lake/packages').resolve()
    assert head(repo) == PIN
    records = json.loads((val/'records.json').read_text())
    assert records['repository_commit'] == PIN
    assert records['validation_plan_sha256'] == sha(BUNDLE/'validation-plan.json')
    manifest = json.loads((repo/'lake-manifest.json').read_text())['packages']
    paths = []
    for p in manifest:
        location = packages/p['name']
        assert head(location) == p['rev'], p['name']
        paths.append(location/'.lake/build/lib/lean')
    for r in records['modules']:
        assert r['returncode'] == 0
        obj = val/'build'/(r['module'].replace('.','/')+'.olean')
        assert sha(obj) == r['olean_sha256'], r['module']
    version = subprocess.check_output([str(lean),'--version'],text=True).strip()
    assert 'version 4.32.0,' in version
    build, logs = val/'examples-build', val/'example-logs'
    build.mkdir(parents=True, exist_ok=True); logs.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    env['LEAN_PATH'] = ':'.join(map(str,[build,val/'build',*paths]))
    checks = []
    def run(name, command, source, input_text=None):
        start = time.monotonic()
        p = subprocess.run(command, cwd=BUNDLE/'examples', env=env, input=input_text,
                           text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = logs/(name+'.log'); log.write_text(p.stdout)
        axioms = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', p.stdout)
        sets = [sorted(x.strip() for x in a.split(',') if x.strip()) for a in axioms]
        standard = all(set(xs) <= {'propext','Classical.choice','Quot.sound'} for xs in sets)
        rec = {'name':name,'returncode':p.returncode,'source_sha256':sha(source),
               'elapsed_seconds':time.monotonic()-start, 'command':command,
               'log':str(log),'axiom_lists':sets,'standard_axioms_only':standard}
        checks.append(rec)
        (val/'example-checks.json').write_text(json.dumps({'repository_commit':PIN,
               'lean_version':version,'checks':checks},indent=2)+'\n')
        print(('PASS' if p.returncode == 0 and standard else 'FAIL'),name,flush=True)
        if p.returncode or not standard:
            print(p.stdout); raise SystemExit(p.returncode or 1)
    plan = json.loads((BUNDLE/'validation-plan.json').read_text())
    for name in plan['examples']:
        source = BUNDLE/'examples'/(name+'.lean')
        command = [str(lean),'-R',str(BUNDLE/'examples'),'-o',str(build/(name+'.olean')),str(source)]
        run(name,command,source)
    specs = json.loads((BUNDLE/'evidence/specifications/source-metrics.json').read_text())
    baseline_axioms = {}
    if args.baseline:
        baseline = args.baseline.resolve()
        br = json.loads((baseline/'build_records.json').read_text())
        assert br['repository_commit'] == PIN
        for r in br['modules']:
            assert r['returncode'] == 0
            assert sha(baseline/'build'/(r['module'].replace('.','/')+'.olean')) == r['olean_sha256']
        env['LEAN_PATH'] = ':'.join(map(str,[baseline/'build',*paths]))
        for s in specs:
            source = repo/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'/(s['module']+'.lean')
            audit = source.read_text()+'\n'+''.join('#print axioms DiophantineConsistency.'+s['module']+'.'+t+'\n' for t in s['targets'])
            run(s['module']+'-before-axioms',[str(lean),'--stdin'],source,audit)
            assert len(checks[-1]['axiom_lists']) == len(s['targets'])
            baseline_axioms[s['module']] = checks[-1]['axiom_lists']
        env['LEAN_PATH'] = ':'.join(map(str,[build,val/'build',*paths]))
    for s in specs:
        source = BUNDLE/'candidates/Computability/DiophantineConsistency/Lean/DiophantineConsistency'/(s['module']+'.lean')
        audit = source.read_text()+'\n'+''.join('#print axioms DiophantineConsistency.'+s['module']+'.'+t+'\n' for t in s['targets'])
        run(s['module']+'-after-axioms',[str(lean),'--stdin'],source,audit)
        assert len(checks[-1]['axiom_lists']) == len(s['targets']), 'Missing printed axiom report'
        if baseline_axioms: assert baseline_axioms[s['module']] == checks[-1]['axiom_lists'], 'Axiom set changed'
    print('Checked',len(plan['examples']),'example/audit modules and',len(specs),'complete-source specification audits.')

if __name__ == '__main__': main()

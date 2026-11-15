#!/usr/bin/env python3
"""Verify this release offline. Use --full for complete source/tape/corpus replay."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent

def need(condition, message):
    if not condition:
        raise RuntimeError(message)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--full', action='store_true')
    parser.add_argument('--output', type=Path, default=ROOT/'replay')
    args = parser.parse_args()
    need(__debug__ and not sys.flags.optimize,
         'Assertions must be enabled. Do not use -O or PYTHONOPTIMIZE.')
    work = args.output.resolve()
    work.mkdir(parents=True, exist_ok=True)
    logs = work/'logs'
    logs.mkdir(exist_ok=True)
    record = {'status':'RUNNING', 'full':args.full, 'checks':[],
              'scope':'Finite artifact verification; not an end-to-end Lean/Rocq proof.'}
    manifest = ROOT/'SHA256SUMS.json'
    need(manifest.exists(), 'Missing release SHA256SUMS.json')
    hashes = json.loads(manifest.read_text())
    for name, expected in hashes.items():
        p = ROOT/name
        need(p.is_file(), 'Missing file: '+name)
        need(digest(p) == expected, 'Hash mismatch: '+name)
    record['manifest_entries'] = len(hashes)
    print(f'Integrity: {len(hashes)} files PASS', flush=True)

    def run(name, script, *extra):
        start = time.monotonic()
        cmd = [sys.executable,'-B',str(ROOT/script),*[str(x) for x in extra]]
        print(name, flush=True)
        result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                text=True, cwd=ROOT)
        (logs/(name+'.txt')).write_text(result.stdout)
        need(result.returncode == 0,
             f'{name} failed ({result.returncode}); see {logs/(name+".txt")}\n'
             +result.stdout[-5000:])
        record['checks'].append({'name':name,'status':'PASS',
                                 'seconds':round(time.monotonic()-start,3)})

    designs = json.loads((ROOT/'comparison/new_designs4.json').read_text())['new_designs']
    for design in designs:
        name = design['name']
        component = 'primary' if name == 'PA194FW' else 'companions'
        path = ROOT/component/'machines'/name/'machine.tm'
        need(digest(path) == design['dense_sha256'], 'Machine hash '+name)
        need(path.read_bytes() == (ROOT/'comparison'/design['table']).read_bytes(),
             'Comparison copy differs: '+name)
        rows = {}
        for line in path.read_text().splitlines():
            if not line.strip() or line.lstrip().startswith('#'):
                continue
            q,b,w,d,n = line.split()
            q,b,w,n = map(int,(q,b,w,n))
            need((q,b) not in rows,'Duplicate row '+name)
            need(w in (0,1) and d in ('L','R') and 0 <= n <= 194,
                 'Invalid action '+name)
            rows[q,b] = w,d,n
        need(set(rows) == {(q,b) for q in range(194) for b in range(2)},
             'Incomplete 194-state binary table '+name)
        seen, todo = set(),[0]
        while todo:
            q = todo.pop()
            if q in seen or q == 194:
                continue
            seen.add(q)
            todo += [rows[q,b][2] for b in (0,1)]
        need(len(seen)==194,'Not all controls graph-reachable '+name)
    record['tables'] = [{'name':d['name'],'states':194,'rows':388,
                         'dense_sha256':d['dense_sha256']} for d in designs]
    print('Four table conventions, hashes and graph reachability PASS',flush=True)

    run('fusion', 'primary/verification/check_fusion_certificates.py',
        '--output',work/'fusion_certificates.json')
    need((work/'fusion_certificates.json').read_bytes() ==
         (ROOT/'primary/machines/PA194FW/fusion_certificates.json').read_bytes(),
         'Regenerated fusion certificates differ')
    run('independent_fusion','research/independent_audit/independent_fusion_audit.py',
        work/'fusion_certificates.json','--output',work/'fusion_audit.json')
    run('command_algebra','primary/verification/check_command_algebra.py',
        '--output',work/'command_algebra.json')
    need((work/'command_algebra.json').read_bytes() ==
         (ROOT/'primary/machines/PA194FW/command_algebra.json').read_bytes(),
         'Regenerated symbolic command contracts differ')
    run('independent_emitter','research/emitter/verify_fusion.py',
        ROOT/'primary/machines/PA194FW/grammar.tree.json',
        '--output',work/'emitter.json')
    run('companions','companions/verify_independent.py',
        '--output',work/'companions.json')
    if args.full:
        run('complete_primary','primary/verify_all.py','--work',work/'primary')
        run('complete_comparison','comparison/verify_comparison.py',
            '--output',work/'comparison.json')
    record['status']='PASS'
    (work/'release_receipt.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record,indent=2))

if __name__ == '__main__':
    main()

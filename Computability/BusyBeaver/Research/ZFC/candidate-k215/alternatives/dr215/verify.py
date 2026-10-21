#!/usr/bin/env python3
"""Offline positive-result replay for the DR215 research packet.

Python standard library only; assertions must be enabled.
--runtime additionally rederives all 6,151 universal DR215 primitive cases.
Search experiments are separate and are not premises of the positive proof.
"""
from pathlib import Path
import argparse, hashlib, json, subprocess, sys, tempfile, time

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('Assertions must be enabled; do not use -O.')
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--runtime', action='store_true')
    ap.add_argument('--work', type=Path)
    args = ap.parse_args()
    started = time.monotonic()
    if args.work:
        work=args.work.resolve(); work.mkdir(parents=True,exist_ok=False)
    else:
        work=Path(tempfile.mkdtemp(prefix='dr215-research-replay-'))
    manifest=json.loads((ROOT/'MANIFEST.json').read_text())
    for item in manifest['files']:
        p=ROOT/item['path']
        assert p.is_file() and p.stat().st_size==item['bytes'],item['path']
        assert digest(p)==item['sha256'],item['path']
    completed=[]
    def run(name,script,*extra):
        result=subprocess.run([sys.executable,'-B',str(ROOT/script),*map(str,extra)],
                              cwd=ROOT,text=True,capture_output=True)
        (work/(name+'.stdout.txt')).write_text(result.stdout)
        (work/(name+'.stderr.txt')).write_text(result.stderr)
        if result.returncode:
            raise RuntimeError(name+' failed; see '+str(work/(name+'.stderr.txt')))
        completed.append(name)
        print(name+': PASS',flush=True)
    core=['--work',work/'DR215']
    if args.runtime:core.append('--runtime')
    run('DR215','DR215/verify.py',*core)
    run('marker-reconstruction','markers/build_marker_family.py','--output',work/'marker_family')
    variants=('m124','m160','m124-m160','m052-m124-m160')
    for variant in variants:
        for name in ('machine.native.tm','machine.tm','state_map.json','verification.json'):
            assert (work/'marker_family'/variant/name).read_bytes()==(ROOT/'markers/marker_family'/variant/name).read_bytes(),(variant,name)
    run('marker-independent-audit','markers/independent/audit.py',
        '--baseline',ROOT/'markers/k215.native.tm','--family',work/'marker_family',
        '--corpus',ROOT/'markers/marker_family/novelty_corpus',
        '--output',work/'independent-marker-audit.json')
    independent=json.loads((work/'independent-marker-audit.json').read_text())
    assert {r['variant'] for r in independent['results']}==set(variants)
    run('marker-frozen-corpus','markers/verify_marker_corpus.py')
    run('late-ZC215-comparison','late_comparison/verify.py',
        '--output',work/'late-comparison.json')
    result={'status':'FULL_RESEARCH_REPLAY_PASS' if args.runtime else 'FINITE_RESEARCH_REPLAY_PASS',
            'runtime_requested':args.runtime,'manifest_files':len(manifest['files']),
            'checks':completed,'seconds':time.monotonic()-started,
            'scope':'Finite literal proof premises; full-runtime flag rederives unbounded symbolic primitive cases. Ordinary calibration and induction proofs are in the report. No proof-assistant kernel endpoint.'}
    (work/'replay.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()

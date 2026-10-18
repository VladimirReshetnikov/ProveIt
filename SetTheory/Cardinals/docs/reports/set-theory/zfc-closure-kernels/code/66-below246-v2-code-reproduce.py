#!/usr/bin/env python3
"""Recheck the packaged mathematical results; expensive synthesis is separate."""
from pathlib import Path
import argparse,hashlib,json,shutil,subprocess,sys,tempfile,time

ROOT=Path(__file__).resolve().parents[1]

def integrity():
    records=(ROOT/'SHA256SUMS').read_text().splitlines()
    for line in records:
        expected,name=line.split('  ',1)
        p=ROOT/name
        assert p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==expected,name
    return len(records)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--full',action='store_true',help='Also rerun the complete direct symbolic replay (about four minutes).')
    ap.add_argument('--skip-integrity',action='store_true',help='For a previously regenerated working copy whose result files have changed.')
    args=ap.parse_args()
    assert __debug__,'Assertions are required; do not use Python -O.'
    (ROOT/'results').mkdir(exist_ok=True)
    records=[];began=time.monotonic()
    if not args.skip_integrity:print('Archive integrity:',integrity(),'files',flush=True)
    def run(label,argv,cwd=ROOT):
        started=time.monotonic()
        result=subprocess.run([sys.executable,'-B',*map(str,argv)],cwd=cwd,text=True,capture_output=True)
        record=dict(label=label,command=list(map(str,argv)),returncode=result.returncode,
                    seconds=time.monotonic()-started,stdout=result.stdout,stderr=result.stderr)
        records.append(record)
        print(label,'PASS'if result.returncode==0 else'FAIL',flush=True)
        if result.returncode:
            print(result.stdout);print(result.stderr,file=sys.stderr)
            raise SystemExit(result.returncode)
    base=ROOT/'reference/context246'
    run('Pristine upstream manifest',[base/'code/check_hashes.py'])
    # The inherited suite refreshes its own result files. Run a disposable copy
    # so that the pinned reference snapshot remains byte-for-byte unchanged.
    with tempfile.TemporaryDirectory(prefix='zfc-baseline-check-')as td:
        copied=Path(td)/'context246';shutil.copytree(base,copied,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
        run('Inherited complete verification',[copied/'code/verify_all.py'],cwd=copied)
    run('Generate and close interval certificate',['code/abstract_program.py'])
    run('Independent exact interval images',['audit/verify_interval_independent.py','results/interval-invariants.json'])
    run('Universal local core and integration obstruction',[
        'search/reductions/code/check_shared_core.py','--baseline',base,
        '--output',ROOT/'results/shared-core-recheck.json'])
    run('Literal scanner first-return witness',[
        'search/scanner/scanner_search.py','--obstruction-only','--output',ROOT/'results/scanner-recheck'])
    run('Register-program bisimulation only',[
        'search/decoder/check_bisimulation_certificate.py',
        'search/decoder/rotation178_bisimulation.json','search/decoder/rotation178_sites_logical.json'])
    run('All saved abstract grammar certificates',['search/grammar/code/validate_grammars.py'])
    run('Rejected rotation bootstrap and bounded witness',['search/grammar/code/replay_rejected_rotation.py'])
    if args.full:run('Complete direct binary symbolic replay',['code/full_symbolic.py'])
    result=dict(status='PASS',full_symbolic_recomputed=args.full,seconds=time.monotonic()-began,
                python=sys.version,scope='Ordinary finite and induction checks; no new Lean/Rocq kernel endpoint.',checks=records)
    (ROOT/'results/reproduction.json').write_text(json.dumps(result,indent=2)+'\n')
    print('ALL REQUESTED RECHECKS PASS',flush=True)

if __name__=='__main__':main()

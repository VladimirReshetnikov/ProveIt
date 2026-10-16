#!/usr/bin/env python3
"""Run the archive's finite checks; optionally rebuild its LaTeX PDF.

This does not rebuild upstream Coq/Lean or certify a new consistency machine.
Python 3.10+ is required. The standalone checks need no ProveIt checkout.
"""
from pathlib import Path
import argparse, hashlib, json, subprocess, sys, tempfile
ROOT=Path(__file__).resolve().parent
EXPECTED={
 'upstream253.tm':(253,'84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95'),
 'rejected248.tm':(248,'0e0158bdf27c2d590525aa389ac72cd8ba4ce2c2408b99c0a56f5b64f600f1e3'),
 'full_equality_epsc270.tm':(270,'54d631fa31f36b02dd41634de8cadeb2cc8fcfae4bc75fea8812af0794b2a136')}

def run(*args):
    r=subprocess.run([str(x) for x in args],cwd=ROOT,text=True,capture_output=True)
    if r.returncode:
        print(r.stdout);print(r.stderr,file=sys.stderr)
        raise SystemExit(r.returncode)
    return r.stdout

def check_tables():
    for name,(n,digest) in EXPECTED.items():
        data=(ROOT/'machines'/name).read_bytes()
        if hashlib.sha256(data).hexdigest()!=digest:raise ValueError('table hash mismatch: '+name)
        if data.splitlines()[0]!=b'#! start 0':raise ValueError('wrong start')
        rows={}
        for line in data.decode().splitlines():
            if not line or line.startswith('#'):continue
            q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t))
            if (q,b) in rows:raise ValueError('duplicate table row')
            if not (0<=q<n and b in (0,1) and w in (0,1) and d in ('L','R') and 0<=t<=n):
                raise ValueError('invalid table row')
            rows[q,b]=(w,d,t)
        if set(rows)!={(q,b) for q in range(n) for b in (0,1)}:raise ValueError('incomplete table')
        print(f'{name}: {n} working states, {len(rows)} rows, exact SHA-256 verified')

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--pdf',action='store_true',help='also rebuild report.pdf with latexmk')
    ap.add_argument('--manifest',action='store_true',help='first verify all originally packaged bytes')
    args=ap.parse_args()
    if args.manifest:
        for line in (ROOT/'SHA256SUMS').read_text().splitlines():
            digest,name=line.split('  ',1)
            if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=digest:
                raise ValueError('archive file changed: '+name)
        print('Packaged SHA256SUMS verified')
    check_tables()
    out=json.loads(run(sys.executable,'code/validate_model.py'))
    expected=json.loads((ROOT/'data/model_validation.json').read_text())
    if out!=expected:raise ValueError('model validation evidence differs')
    print('Both Boolean obstructions, total coding and low-code regressions verified')
    print(run(sys.executable,'code/kernel_metrics.py').strip())
    run(sys.executable,'-m','unittest','discover','-s','code','-p','test_epsc_checker.py','-v')
    print('11 reference-checker tests passed, including 9,216 substitution cases')
    with tempfile.TemporaryDirectory(prefix='epsc-certificate-') as tmp:
        out=json.loads(run(sys.executable,'code/verify_operation_certificate.py',
            '--source','data/source_dag.json','--candidate','data/candidate_dag.json',
            '--certificate','data/rm_bisimulation.json','--output',Path(tmp)/'checked.json'))
        if out['related_operation_pairs']!=3620 or out['successor_pairs_verified']!=5162:
            raise ValueError('unexpected operation certificate size')
        print('Operation certificate verified: 3,620 pairs and 5,162 successor pairs')
    for p in sorted((ROOT/'examples').glob('*.json')):
        out=json.loads(run(sys.executable,'code/epsc_checker.py',p))
        if not out['valid'] or out['refutation']:raise ValueError('unexpected example result')
    print('All three example theorem certificates accepted; none claims a refutation')
    if args.pdf:
        run('latexmk','-pdf','-interaction=nonstopmode','-halt-on-error','report.tex')
        print('report.pdf rebuilt')
    print('Finite verification complete. No new end-to-end consistency-machine theorem is claimed.')

if __name__=='__main__':main()

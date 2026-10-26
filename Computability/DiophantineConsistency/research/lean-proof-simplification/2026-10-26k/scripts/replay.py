#!/usr/bin/env python3
"""Replay isolated proofs, optionally the complete pairing example.

Requires an existing ProveIt checkout at the recorded commit with Lean 4.32.0
and its mathlib cache. Does not install dependencies or modify that checkout.
Recorded evidence is separate from newly generated replay results.
"""
from pathlib import Path
import argparse, hashlib, json, os, shutil, subprocess, sys, tempfile, time

PACKET = Path(__file__).resolve().parents[1]
BASE = '6175dff9a15491497c7a3c1bda4f6a62a6349c74'
SRC = Path('Computability/DiophantineConsistency/Lean')

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--project', type=Path, required=True)
    p.add_argument('--lake', default='lake')
    p.add_argument('--full-pairing', action='store_true')
    p.add_argument('--out', type=Path, default=PACKET/'replay-results')
    args = p.parse_args()
    project = args.project.resolve(); out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    def capture(command):
        return subprocess.run(command, cwd=project, check=True, text=True,
                              stdout=subprocess.PIPE).stdout.strip()
    head = capture(['git', 'rev-parse', 'HEAD'])
    if head != BASE:
        raise SystemExit(f'Expected repository {BASE}, found {head}. Use an isolated checkout at the pin.')
    # Obtain Lake's environment privately; no environment values are written to logs.
    env = json.loads(capture([args.lake, 'env', 'python3', '-c',
                             'import os,json;print(json.dumps(dict(os.environ)))']))
    lean = shutil.which('lean', path=env.get('PATH'))
    if not lean:
        raise SystemExit('Lake environment does not provide lean.')
    version = subprocess.run([lean, '--version'], cwd=project, env=env, check=True,
                             capture_output=True, text=True).stdout.strip()
    if 'version 4.32.0,' not in version:
        raise SystemExit(f'Expected Lean 4.32.0; found {version}')
    records = []
    def run(label, cmd, source=None):
        start=time.monotonic()
        r=subprocess.run([str(x) for x in cmd],cwd=project,env=env,
                         capture_output=True,text=True)
        (out/(label+'.log')).write_text(r.stdout+r.stderr)
        entry=dict(name=label,returncode=r.returncode,seconds=time.monotonic()-start,
                   log=label+'.log',command=[str(x) for x in cmd])
        if source:
            entry['source_sha256']=hashlib.sha256(Path(source).read_bytes()).hexdigest()
        records.append(entry)
        print(f'{label}: {"PASS" if r.returncode == 0 else "FAIL"}')
        if r.returncode:
            save(); raise SystemExit(r.returncode)
    def save():
        (out/'results.json').write_text(json.dumps(dict(repository=head,lean=version,
            full_pairing_requested=args.full_pairing,checks=records),indent=2)+'\n')
    with tempfile.TemporaryDirectory(prefix='diophantine-proof-review-') as tmp:
        tmp=Path(tmp);(tmp/'DiophantineConsistency').mkdir()
        env['LEAN_PATH']=str(tmp)+os.pathsep+env.get('LEAN_PATH','')
        helper_roots=[PACKET/'certificates/lean', PACKET/'projection-and-budget/lean']
        for root,names in [(helper_roots[0],['ArithmeticCertificates']),
                           (helper_roots[1],['PairingProjection','AffineBudget'])]:
            for name in names:
                source=root/'DiophantineConsistency'/(name+'.lean')
                run('helper-'+name,[lean,'-R',root,'-o',tmp/'DiophantineConsistency'/(name+'.olean'),source],source)
        checks=[PACKET/'certificates/lean/ArithmeticCertificatesChecks.lean',
                PACKET/'projection-and-budget/lean/PairingProjectionChecks.lean',
                PACKET/'projection-and-budget/lean/AffineBudgetChecks.lean',
                PACKET/'native-proofs/OneHotSupport.lean',
                PACKET/'native-proofs/SignedModEq.lean']
        for source in checks:run(source.stem,[lean,source],source)
        if args.full_pairing:
            root=project/SRC
            for name in ['Representation','ArithmeticRepresentation','ComposeRepresentation']:
                source=root/'DiophantineConsistency'/(name+'.lean')
                run('base-'+name,[lean,'-R',root,'-o',tmp/'DiophantineConsistency'/(name+'.olean'),source],source)
            root=PACKET/'projection-and-budget/patched-modules'/SRC
            source=root/'DiophantineConsistency/PairingRepresentation.lean'
            run('patched-PairingRepresentation',[lean,'-R',root,'-o',
                tmp/'DiophantineConsistency/PairingRepresentation.olean',source],source)
            source=PACKET/'projection-and-budget/lean/PairingDataAudit.lean'
            run('pairing-data-audit',[lean,source],source)
        for name in ['conservative','with-sign-algebra']:
            run('patch-'+name,['git','apply','--check',PACKET/'patches'/(name+'.patch')])
    save()
    print('Completed recorded-scope replay; this is not a full repository build.')

if __name__=='__main__':main()

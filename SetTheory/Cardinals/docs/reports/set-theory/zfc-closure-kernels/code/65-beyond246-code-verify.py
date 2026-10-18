#!/usr/bin/env python3
"""Replay the portable research packet without downloading dependencies.

Checks written certificates and witnesses, including the full relational
invariant. Does not rerun the long synthesis/search families. Use
--replay-ledger to re-execute all 130,872 saved single-incoming failures.
The reference verifier is run in a disposable copy so its published bytes stay
unchanged. This is not a Lean/Rocq build or a lower-bound proof.
"""
from pathlib import Path
import argparse, hashlib, importlib.util, json, shutil, subprocess, sys, tempfile, time

ROOT=Path(__file__).resolve().parents[1]

def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def manifest(path):
    count=0
    for line in path.read_text().splitlines():
        digest,name=line.split('  ',1)
        assert not Path(name).is_absolute() and '..' not in Path(name).parts
        p=path.parent/name
        assert p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==digest,name
        count+=1
    return count

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path)
    ap.add_argument('--replay-ledger',action='store_true')
    ap.add_argument('--skip-reference',action='store_true',help='Skip the existing 246 reference suite only.')
    args=ap.parse_args()
    if not __debug__:ap.error('Assertions required; do not use -O or -OO.')
    out=args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix='zfc-beyond246-verification-'))
    out.mkdir(parents=True,exist_ok=True)
    started=time.monotonic();records=[]
    if (ROOT/'SHA256SUMS').exists():
        records.append(dict(check='packet integrity',status='PASS',files=manifest(ROOT/'SHA256SUMS')))
    for relative in ['baseline246/zfc-context246/SHA256SUMS','alternative/SHA256SUMS']:
        records.append(dict(check=relative,status='PASS',files=manifest(ROOT/relative)))
    def run(name,command,cwd):
        began=time.monotonic()
        print('Running:',name,flush=True)
        result=subprocess.run(command,cwd=cwd,text=True,capture_output=True)
        record=dict(check=name,command=command,returncode=result.returncode,seconds=time.monotonic()-began,stdout=result.stdout,stderr=result.stderr)
        records.append(record)
        if result.returncode:
            print(result.stdout);print(result.stderr,file=sys.stderr)
            (out/'verification-summary.json').write_text(json.dumps(dict(status='FAIL',checks=records),indent=2)+'\n')
            raise SystemExit(result.returncode)
        print('PASS:',name,flush=True)
    extra=['--replay-ledger'] if args.replay_ledger else []
    run('new saved results, domain coverage and solver positive control',[sys.executable,'-B','code/check_saved_results.py',*extra,'--output',str(out/'saved-results.json')],ROOT)
    run('independent literal prepared-phase and return-origin witnesses',[sys.executable,'-B','audit/verify_audit.py','--output',str(out/'audit')],ROOT)
    run('context support, 8391-case affine reference and small scanner witnesses',[sys.executable,'-B','check_support.py'],ROOT/'context')
    print('Running: independent product and 7.7-million-vector invariant verification',flush=True)
    began=time.monotonic();v=module('independent_invariant',ROOT/'alternative/verify_invariant.py')
    sites,cases=v.source_graph()
    invariants=dict(status='PASS',product=v.check_product(cases),relational=v.check_relational(sites,cases),seconds=time.monotonic()-began)
    assert invariants['relational']['checked_abstract_edges']==8669994
    (out/'invariants.json').write_text(json.dumps(invariants,indent=2)+'\n')
    records.append(dict(check='independent product and relational invariants',status='PASS',seconds=invariants['seconds']))
    print('PASS: independent product and relational invariants',flush=True)
    if not args.skip_reference:
        with tempfile.TemporaryDirectory(prefix='zfc246-reference-check-') as temp:
            reference=Path(temp)/'zfc-context246'
            shutil.copytree(ROOT/'baseline246/zfc-context246',reference)
            run('complete inherited reference suite in temporary copy',[sys.executable,'-B','code/verify_all.py'],reference)
            shutil.copy2(reference/'results/verification-summary.json',out/'reference-verification-summary.json')
    summary=dict(status='PASS',seconds=time.monotonic()-started,python=sys.version,one_incoming_journal_replayed=args.replay_ledger,reference_suite_replayed=not args.skip_reference,new_sub246_machine_claimed=False,scope='Finite witness replays, checked inductive certificates and bounded-search records; not a proof-assistant build or state lower bound.',checks=records)
    (out/'verification-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print('ALL REQUESTED VERIFICATIONS PASS',flush=True)
    print('Verification records:',out,flush=True)

if __name__=='__main__':main()

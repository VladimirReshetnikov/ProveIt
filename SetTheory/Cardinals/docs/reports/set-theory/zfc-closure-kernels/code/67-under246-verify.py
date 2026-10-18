#!/usr/bin/env python3
"""Replay the packet's principal certificates in a disposable working copy.

Python 3.10+ standard library only. Run from any directory. Expensive discovery
searches and external proof-assistant builds are deliberately separate.
"""
from __future__ import annotations
import argparse, gzip, hashlib, json, os, shutil, subprocess, sys, tempfile, time
from pathlib import Path

ROOT=Path(__file__).resolve().parent

def check_manifest():
    path=ROOT/'manifest.json'
    if not path.exists():raise SystemExit('Missing manifest.json; use the complete research packet.')
    d=json.loads(path.read_text());count=0
    for name,wanted in d['sha256'].items():
        p=ROOT/name
        if not p.is_file():raise AssertionError(('missing delivered file',name))
        actual=hashlib.sha256(p.read_bytes()).hexdigest()
        if actual!=wanted:raise AssertionError(('changed delivered file',name,wanted,actual))
        count+=1
    return count

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--full',action='store_true',help='Also rerun the entire unchanged incoming prefix246 suite.')
    ap.add_argument('--output',type=Path,help='Optional JSON record; existing research artifacts are not modified.')
    args=ap.parse_args()
    if not __debug__:ap.error('Assertions must be enabled; do not use -O or -OO.')
    began=time.monotonic();count=check_manifest();checks=[]
    with tempfile.TemporaryDirectory(prefix='zfc-under246-replay-') as tmp:
        work=Path(tmp)
        shutil.copytree(ROOT/'research',work/'research')
        # The 48 MiB original ledger is distributed in its lossless compressed
        # form; the unchanged independent partition checker expects plain JSON.
        ledger=work/'research/agent_state/incoming_extended_compensating_search.json'
        if not ledger.exists():ledger.write_bytes(gzip.decompress(Path(str(ledger)+'.gz').read_bytes()))
        tasks=[
            ('source_bisimulation',['research/agent_logic/verify_reassociation.py']),
            ('rotated246_full_certificate',['research/agent_logic/verify_rotated246.py']),
            ('incoming_action_partition',['research/agent_state/check_compensating_partition.py']),
            ('dirty_root_postfixpoint',['research/agent_logic/abstract_cfg.py','--K','8']),
            ('propositional_countermodel',['research/agent_logic/specialized_axiom_countermodel.py']),
            ('opaque_macro_counterexample',['research/agent_state/check_oracle_counterexample.py']),
            ('literal_bad245_frame',['research/root_search/literal_rebracket_counterexample.py']),
        ]
        extra=work/'research/agent_state/rebracket/check_synthesis201_certificate.py'
        if extra.exists():tasks.append(('three_row_partition_and_rejections',[str(extra.relative_to(work)),'--replay']))
        if args.full:tasks.append(('original_prefix246_full_suite',['research/sources/context246/zfc-context246/code/verify_all.py']))
        env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1'
        env['ZFC246_SOURCE']=str(work/'research/sources/context246/zfc-context246')
        for name,command in tasks:
            started=time.monotonic()
            result=subprocess.run([sys.executable,'-B',*command],cwd=work,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
            record=dict(name=name,status='PASS' if result.returncode==0 else 'FAIL',returncode=result.returncode,seconds=round(time.monotonic()-started,4),output=result.stdout)
            checks.append(record);print(f'{name}: {record["status"]}',flush=True)
            if result.returncode:
                print(result.stdout)
                raise AssertionError(('certificate replay failed',name))
        # Check the user-facing machine copy agrees with the independently
        # regenerated canonical artifact, without relying on its filename.
        regenerated=work/'research/agent_logic/rotated246/zfc_rotated246.tm'
        assert regenerated.read_bytes()==(ROOT/'machines/zfc_rotated246.tm').read_bytes()
    out=dict(status='PASS',delivered_files_hashed=count,checks=checks,
        canonical_machine_sha256=hashlib.sha256((ROOT/'machines/zfc_rotated246.tm').read_bytes()).hexdigest(),
        working_states=246,strictly_fewer_than246_established=False,
        new_kernel_build_performed=False,full_incoming_suite=args.full,
        elapsed_seconds=round(time.monotonic()-began,4))
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='checks'},indent=2))

if __name__=='__main__':main()

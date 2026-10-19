#!/usr/bin/env python3
"""Replay exact, finite grammar evidence; does not rerun heuristic searches."""
from __future__ import annotations
import argparse, hashlib, json, subprocess, sys, tempfile
from pathlib import Path
from check_grammar import check
from verify_zero5_bootstrap_obstruction import verify as obstruction
ROOT=Path(__file__).resolve().parent

def main():
    if not __debug__:raise RuntimeError('Assertions must be enabled; do not use -O.')
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path);a=p.parse_args()
    out=a.output.resolve()if a.output else Path(tempfile.mkdtemp(prefix='zfc-grammar-replay-'))
    if out.exists()and any(out.iterdir()):p.error('--output must be new or empty.')
    out.mkdir(parents=True,exist_ok=True)
    regenerated=out/'regenerated'
    subprocess.run([sys.executable,'-B',str(ROOT/'canonicalize_inputs.py'),'--output',str(regenerated)],check=True)
    hashes={}
    for file in sorted(regenerated.iterdir()):
        assert file.read_bytes()==(ROOT/'inputs'/file.name).read_bytes(),file.name
        hashes[file.name]=hashlib.sha256(file.read_bytes()).hexdigest()
    exact=obstruction(ROOT/'reference_data')
    assert exact==json.loads((ROOT/'results/zero5-bootstrap-obstruction.json').read_text())
    (out/'zero5-bootstrap-obstruction.json').write_text(json.dumps(exact,indent=2)+'\n')
    cases=[('canonical-20262021.json',54,128,6),('canonical-dynamic.json',54,128,6),
           ('canonical-free-zero6.json',0,128,6),('canonical-free-zero7.json',0,128,7),
           ('canonical-milp24.json',54,128,6),('canonical-milp32-warm.json',54,128,6),
           ('canonical-relax50-seed.json',50,128,6),('canonical-zero5-relax50.json',50,134,6),
           ('canonical-zero5-relax50-targeted.json',50,138,5),('canonical-zero5-final.json',50,136,5)]
    baseline=json.loads((ROOT/'inputs/canonical-baseline.json').read_text())
    resume=(ROOT/'inputs/canonical-resume.txt').read_text().splitlines()
    n=int(resume[0]);expected={}
    for row in resume[1:n+1]:
        k,w=row.split();expected[w]=(w[:int(k)],w[int(k):])
    assert {w:(a,b)for w,a,b in baseline['rules']}==expected
    assert [r['word']for r in baseline['routes']]==resume[n+2:]
    records=[check(ROOT/'inputs/canonical-baseline.json',required_locks=54)]
    for name,locks,n,z in cases:
        record=check(ROOT/'candidates'/name,required_locks=locks)
        assert(record['grammar_rules'],record['source_maximum_zero_run'])==(n,z)
        records.append(record)
        print(name,record['grammar_rules'],'rules; zero run',record['source_maximum_zero_run'],flush=True)
    result=dict(status='PASS_FINITE_GRAMMAR_RESEARCH',candidate_checks=records,
                regenerated_input_hashes=hashes,exact_forced_leading_zero_depth=6,
                scope='Does not assert a new machine below 245, rerun heuristic optimization, or replace literal-machine runtime/bootstrap certification.')
    (out/'grammar-verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(out/'grammar-verification.json')
if __name__=='__main__':main()

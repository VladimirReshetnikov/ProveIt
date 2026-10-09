"""Rerun the exact literal case requests in the saved propagation audit.

This includes the slow capped figure-eight request by default. Use --case NAME
to select one saved case. Outputs go to results/reproduced; golden inputs are
never overwritten. Timings are diagnostic, while decisions and counters are
compared to the recorded source-fixed run.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys
from time import perf_counter

ROOT=Path(__file__).resolve().parents[1]
FAST=ROOT/'work/fast' if (ROOT/'work/fast').exists() else ROOT/'fast'
sys.path.insert(0,str(FAST))
from fastunknot.integer_codec import json_safe
from fastunknot.normal_propagation import search_positive_euler
from fastunknot.normal_propagation_verify import verify_normal_propagation_certificate


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case',action='append',default=[])
    parser.add_argument('--output',type=Path,default=ROOT/'results/reproduced/propagation_cases.json')
    args=parser.parse_args()
    source=ROOT/'results/propagation_audit.json'
    if args.output.resolve()==source.resolve():
        parser.error('refusing to overwrite the golden propagation audit')
    golden=json.loads(source.read_text())
    available={r['name'] for r in golden['cases']}
    if set(args.case)-available:
        parser.error('unknown case; available names: '+', '.join(sorted(available)))
    records=[]
    for case in golden['cases']:
        if args.case and case['name'] not in args.case:
            continue
        start=perf_counter()
        answer=search_positive_euler(case['triangulation'],**case['options'])
        elapsed=perf_counter()-start
        assert answer['status']==case['answer']['status'], case['name']
        assert answer['stats']==case['answer']['stats'], (case['name'],'counter mismatch')
        if answer.get('certificate') is not None:
            assert verify_normal_propagation_certificate(case['triangulation'],answer['certificate'])
        records.append(dict(name=case['name'],status=answer['status'],
                            stats=answer['stats'],seconds=elapsed,answer=answer))
        print(case['name'],answer['status'],flush=True)
    result=dict(schema='propagation-case-reproduction-v1',
                source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                scope='literal saved case requests; exact decisions and counters; diagnostic elapsed time',
                cases=records)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n')


if __name__=='__main__':
    main()

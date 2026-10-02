"""Extra exact regressions for the general critical coefficient implementation.

Expected values are derived from the first possible rotational and capacity
grades, together with cancellation of pure label-collision terms. No fitting.
Run beside general_coefficients.py, or pass --source and --output explicitly.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse,importlib.util,json,hashlib

def run(source):
    spec=importlib.util.spec_from_file_location('general_coefficients',source)
    gc=importlib.util.module_from_spec(spec);spec.loader.exec_module(gc)
    rows=[]
    for s in [1,-1]:
        for ell,k,want in [(5,1,{}),(5,2,{}),(5,3,{1:F(4,5)-F(s,2)}),
                           (6,2,{1:F(1,3)}),(6,3,{}),(8,2,{}),(8,3,{}),
                           (9,3,{1:F(2,9)})]:
            got=gc.critical_coefficient(ell,k,s)
            assert got==want,(ell,k,s,got,want)
            rows.append({'ell':ell,'order':k,'sign':s,'lambda_exponent_map':gc.show(got)})
    stirling={(0,0):1};partition_checks=0
    for m in range(1,11):
        for k in range(1,m+1):
            stirling[m,k]=stirling.get((m-1,k-1),0)+k*stirling.get((m-1,k),0)
        for D in range(min(m,4)):
            terms=list(gc.partitions_with_deficit((2,)*m,D))
            assert len(terms)==sum(stirling.get((m,m-d),0) for d in range(D+1))
            assert all(len(blocks)==m-d and sum(blocks)==2*m for blocks,d in terms)
            partition_checks+=1
    return {'scope':'Exact rational algorithm regressions and Stirling-number partition counts; not a proof of uniform asymptotic remainders.',
            'coefficient_source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
            'additional_grade_checks':rows,'partition_count_checks':partition_checks,
            'partition_max_slots':10,'partition_max_deficit':3}

if __name__=='__main__':
    root=Path(__file__).resolve().parent
    ap=argparse.ArgumentParser()
    ap.add_argument('--source',type=Path,default=root/'general_coefficients.py')
    ap.add_argument('--output',type=Path,default=root.parent/'results/additional-critical-grades.json')
    args=ap.parse_args();out=run(args.source)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print('PASS: 16 additional critical-grade regressions and',out['partition_count_checks'],'partition-count checks')

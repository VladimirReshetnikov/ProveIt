#!/usr/bin/env python3
"""Regenerate the exact arithmetic and finite-kernel verification receipts.

Use --optimized to run each checker with Python's optimization flag as well;
the output must be unchanged. No network or third-party packages are used.
"""
import argparse,json,subprocess,sys
from pathlib import Path


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--optimized',action='store_true')
    args=parser.parse_args()
    here=Path(__file__).resolve().parent
    results=here.parent/'results';results.mkdir(exist_ok=True)
    jobs=[('certify.py','certificate.json',False),
          ('verify_affine9.py','affine9_independent.json',True),
          ('verify_portfolio13.py','portfolio13_independent.json',True),
          ('verify_rejected_routes.py','scoped_obstructions.json',True),
          ('check_integration.py','integration_checks.json',True),
          ('verify_kernel.py','kernel_checks.json',True)]
    receipts=[]
    for script,name,explicit_output in jobs:
        target=results/name
        command=[sys.executable,str(here/script)]
        if explicit_output:command+=['--output',str(target)]
        normal=subprocess.run(command,cwd=here,check=True,text=True,capture_output=True)
        if not explicit_output:target.write_text(normal.stdout)
        data=json.loads(target.read_text())
        if data.get('status') not in ('PASS','passed'):
            raise RuntimeError('Checker status failed: '+script)
        if args.optimized:
            optimized=subprocess.run([sys.executable,'-O',*command[1:]],cwd=here,
                                     check=True,text=True,capture_output=True)
            if normal.stdout!=optimized.stdout:
                raise RuntimeError('Optimization changed checker output: '+script)
        receipts.append({'script':script,'result':name,'status':'PASS',
                         'optimized_stdout_identical':args.optimized})
        print(script+': PASS')
    a=json.loads((results/'certificate.json').read_text())['portfolios']
    b=json.loads((results/'affine9_independent.json').read_text())
    c=json.loads((results/'portfolio13_independent.json').read_text())
    for primary,independent in zip(a,[b,c]):
        for pkey,ikey in [('Q','maximum_squared_norm'),('tuples_checked','tuples_checked'),
                          ('squared_norm_sum','sum_of_squared_norms')]:
            if primary[pkey]!=independent[ikey]:raise RuntimeError('Independent certificate disagreement')
    (results/'reproduction.json').write_text(json.dumps({'status':'PASS','checks':receipts,
      'independent_certificate_comparison':'PASS','scope':'Finite certificates, exact schedule arithmetic, scoped identities, and small graph contractions. Not an end-to-end SAT solver.'},indent=2)+'\n')
    print('Independent certificate comparison: PASS')


if __name__=='__main__':main()

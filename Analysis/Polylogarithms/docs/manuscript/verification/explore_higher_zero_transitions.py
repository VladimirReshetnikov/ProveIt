"""Propose sixth/seventh-index root brackets; never certify completeness.

This exploratory stage uses floating point. Acceptance is a separate exact
Euler--Maclaurin sign replay plus a global multiplicity/critical-point proof.
"""
from pathlib import Path
import importlib.util, json, sys, time
import mpmath as mp

B=Path(__file__).resolve().parents[1]
source=B.parent/'reports/relation-cm-zero-transitions/code/explore_zeros.py'
spec=importlib.util.spec_from_file_location('zero_experiment',source)
core=importlib.util.module_from_spec(spec);spec.loader.exec_module(core)
mp.mp.dps=60
core.ETAB[:]=[core.es(k,core.NMAX) for k in range(80)]
rows=[];start=time.monotonic()
for n in [6,7]:
    for k in range(1,7):
        points=sorted(set([mp.mpf(j)/160 for j in range(64,561)] +
            [mp.power(10,-3+mp.mpf(j)*9/240) for j in range(241)]))
        values=[core.value(n,a,k) for a in points]
        brackets=[(points[j],points[j+1]) for j in range(len(points)-1)
                  if values[j]*values[j+1]<0]
        roots=[mp.findroot(lambda a:core.value(n,a,k),pair,solver='anderson')
               for pair in brackets]
        row=dict(n=n,k=k,roots=[mp.nstr(r,48) for r in roots],
                 sampled_sign_changes=len(roots),scope='Numerical bracket proposals only.',
                 elapsed_seconds=time.monotonic()-start)
        rows.append(row)
        print(json.dumps(row),flush=True)
        (B/'verification/higher-zero-proposals.json').write_text(json.dumps(
            dict(working_digits=60,scan_points=len(points),range=['1e-3','1e6'],
                 rows=rows,complete=False),indent=2)+'\n',encoding='utf-8')
        if len(roots)==n:break

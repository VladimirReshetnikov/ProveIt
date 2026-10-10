"""Replay every new sixth/seventh-index sign with a second implementation.

The independent engine uses rising-factorial coefficient multiplication,
100-digit outward integer intervals, and a different Hurwitz cutoff. No
floating-point root proposal or sign is trusted.
"""
from pathlib import Path
from fractions import Fraction
import hashlib, importlib.util, json, sys

sys.dont_write_bytecode=True
B=Path(__file__).resolve().parents[1]
source=B.parent/'reports/lerch-zero-bifurcations/verification/certify.py'
spec=importlib.util.spec_from_file_location('higher_zero_independent',source)
core=importlib.util.module_from_spec(spec)
sys.modules[spec.name]=core;spec.loader.exec_module(core)
# At the new narrow brackets, the delivered engine's 55-digit default
# rounds very small high Bernoulli powers to a visibly wide interval after
# multiplying by large rising factorials. Increase precision rather than
# replacing a failed sign enclosure with a numerical decision.
core.DIGITS=100;core.SCALE=10**core.DIGITS;core.LOG_TERMS=128
original=json.loads((B/'verification/higher-zero-certificates.json').read_text())
checks=[]
for r in original['certificates']:
    n,k=r['n'],r['k'];lo,hi=map(Fraction,r['bracket'])
    for side,a in [('left',lo),('right',hi)]:
        val,error=core.certify_F(n,k,a)
        assert val.sign()==r[side+'_sign'],(n,k,r['j'],side)
        checks.append(dict(n=n,k=k,j=r['j'],kind=side,
            interval=val.json(),analytic_error=error.json(),sign=val.sign()))
    if k>1:
        val,error=core.certify_F(n,k-1,core.I.bounds(lo,hi))
        assert val.sign()==r['previous_order_sign'],(n,k,r['j'],'critical interval')
        checks.append(dict(n=n,k=k-1,j=r['j'],kind='critical interval',
            interval=val.json(),analytic_error=error.json(),sign=val.sign()))
    print(n,k,r['j'],'independent signs passed',flush=True)
result=dict(status='PASS',source='../'+source.relative_to(B.parent).as_posix(),
    source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
    engine='Independent rising-factorial coefficient Euler--Maclaurin engine',
    fixed_denominator=str(core.SCALE),log_series_terms=core.LOG_TERMS,
    initial_hurwitz_terms=32,bernoulli_orders=16,
    input_sha256=hashlib.sha256((B/'verification/higher-zero-certificates.json').read_bytes()).hexdigest(),
    endpoint_checks=sum(c['kind'] in ['left','right'] for c in checks),
    critical_interval_checks=sum(c['kind']=='critical interval' for c in checks),
    checks=checks,scope='Exact independent sign replay; the global theorem also uses the written multiplicity and critical-point descent proofs.')
(B/'verification/higher-zero-independent.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('PASS:',len(checks),'independent rational enclosures.')

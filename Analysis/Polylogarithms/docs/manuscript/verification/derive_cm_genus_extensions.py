"""Exact new genus-ratio formulas and uniform quadratic-degree witnesses.

Uses the separately certified genus factors and seed ratios, then performs
only rational-pair arithmetic. Nonvanishing, period normalization and CM
Galois propagation retain their separate analytic proof obligations.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib, importlib.util, json, sys
sys.dont_write_bytecode=True
B=Path(__file__).resolve().parents[1]
source=B.parent/'reports/relation-cm-zero-transitions/code/verify_genus_arithmetic.py'
spec=importlib.util.spec_from_file_location('cm_pair_algebra',source)
c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
zero=(F(0),F(0));one=(F(1),F(0))
def norm(pair,e):return pair[0]**2-e*pair[1]**2
rows=[]
for D,e,A,u,t,Hplus,r4,r6 in c.DATA:
    Hminus=[(a,-b) for a,b in Hplus]
    period=c.multiply((A**6,F(0)),c.power(u,-t,e),e)
    for w,beta,seed in [(12,F(432000,691),one),(16,F(3456000,3617),r4),
                         (18,F(9504000,43867),r6)]:
        ratio=c.absolute(c.quotient(c.evaluate(Hplus,beta),c.evaluate(Hminus,beta),e),e)
        value=c.multiply(c.multiply(seed,period,e),ratio,e)
        assert c.is_positive(value,e)
        assert norm(value,e)==A**w and c.is_positive((value[0],-value[1]),e)
        rows.append(dict(D=D,positive_discriminant=e,weight=w,
            beta=str(beta),value=c.pair_json(value),norm=str(norm(value,e)),passed=True))

N=10;M=20
def bound(form,p,y0=F(1),omit_axis_unit=False):
    a,b,d=form
    def q(m,n):return F(a*m*m-b*m*n+d*n*n,a)
    omitted={(0,0)}|({(1,0),(-1,0)} if omit_axis_unit else set())
    finite=sum((q(m,n)**(-p) for n in range(-N,N+1)
        for m in range(-M,M+1) if (m,n) not in omitted),F(0))
    if p==2:tail_n=F(2,3*N**3)/y0**4+F(2,N**2)/y0**3
    else:
        assert p==6
        tail_n=F(2,11*N**11)/y0**12+F(63,320*N**10)/y0**11
    tail_m=F(4*N,2*p-1)/(F(M)-F(N,2))**(2*p-1)
    tail_axis=F(2,(2*p-1)*M**(2*p-1))
    return finite+tail_n+tail_m+tail_axis

# All nonzero vectors in reduced lattices have norm >= 1. Bounds on the
# fourth-power absolute sum therefore hold at every even weight >= 4.
caps=[]
for form,y0,cap in [((2,1,2),F(9,10),F(8)),((2,2,3),F(1),F(5))]:
    value=bound(form,2,y0)
    assert value<cap
    caps.append(dict(form=form,power=4,total_bound=str(value),upper=str(cap)))
assert F(7,160)>F(1,32) and F(7,100)>F(1,16)

# At D=-39 there are only two unit vectors, +-1; all others have norm >1.
# The weight-12 non-axis sums majorize every weight 12m, m>=1.
for form,cap in [((1,1,10),F(1,2)),((2,1,5),F(1,2)),((3,3,4),F(3,4))]:
    value=bound(form,6,omit_axis_unit=True)
    assert value<cap
    caps.append(dict(form=form,power=12,nonunit_tail=str(value),upper=str(cap)))
assert F(3,10)>F(3,4)**6
report=dict(status='PASS',arithmetic='Exact Python fractions and quadratic pairs',
    source='../'+source.relative_to(B.parent).as_posix(),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
    new_ratio_formulas=rows,lattice_bounds=caps,
    rational_exclusion_margins={'-15':'7/160 > (1/2)^5','-20':'7/100 > (1/2)^4','-39':'3/10 > (3/4)^6'},
    scope='Exact coefficient identities and lattice caps. The norm/conjugation theorem and its all-weight degree consequence require the written analytic and CM arguments.')
(B/'verification/CM-genus-extensions.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in report.items() if k!='lattice_bounds'},indent=2))

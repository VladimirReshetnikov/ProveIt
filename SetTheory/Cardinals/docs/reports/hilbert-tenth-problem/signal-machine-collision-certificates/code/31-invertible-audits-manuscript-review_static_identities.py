#!/usr/bin/env python3
"""Fresh static rational identities; no source imports, simulation, or event selection."""
from fractions import Fraction as Q
from functools import reduce
from pathlib import Path
import hashlib
import json

OUT = Path(__file__).resolve().parent
checks = []
def equal(name, a, b):
    assert a == b, (name, a, b)
    checks.append(name)
def L(x=0, y=0):
    return (Q(x), Q(y))
def add(a, b):
    return tuple(x+y for x,y in zip(a,b))
def sub(a, b):
    return tuple(x-y for x,y in zip(a,b))
def mul(c, a):
    return tuple(Q(c)*x for x in a)
def line(slope, intercept, t):
    return add(mul(slope,t),intercept)
def norm(a,k):
    return a[0]*k+a[1]
def matmul(a,b):
    return [[sum(a[i][k]*b[k][j] for k in range(len(b))) for j in range(len(b[0]))] for i in range(len(a))]

x,y = L(1,0),L(0,1)
F = L('-2/3','5/6')
xi = L(-1,'5/4')
times = [L(), x, L('5/3'), L('19/9'), L('17/9','1/2'),L('35/9'),L('29/9','5/6'),L('23/9','5/3')]
q_end = [L(),x,L(),L('4/9'),L('1/2','-1/8'),L(),F,L()]
z_end = [x,x,L('2/3'),L('4/9'),y,xi,F,F]
q_lines = [(Q(1),L()),(Q('-3/2'),L('5/2')),(Q(1),L('-5/3')),(Q('-1/4'),L('35/36')),(Q('-1/4'),L('35/36')),(Q(1),L('-35/9')),(Q(-1),L('23/9','5/3'))]
z_lines = [(Q(0),x),(Q('-1/2'),L('3/2')),(Q('-1/2'),L('3/2')),(Q(2),L('-34/9')),(Q('-1/2'),L('17/18','5/4')),(Q('-1/2'),L('17/18','5/4')),(Q(0),F)]
durations = [x,L('2/3'),L('4/9'),L('-2/9','1/2'),L(2,'-1/2'),F,F]
for j in range(7):
    equal(f'duration {j+1}',sub(times[j+1],times[j]),durations[j])
    for name, lines, ends in [('q',q_lines,q_end),('X',z_lines,z_end)]:
        slope, intercept=lines[j]
        equal(f'{name} line {j+1} left endpoint',line(slope,intercept,times[j]),ends[j])
        equal(f'{name} line {j+1} right endpoint',line(slope,intercept,times[j+1]),ends[j+1])
# An affine function with nonnegative endpoint values and not both zero is
# positive on the whole open interval. This is a finite proof, not sampling.
endpoint_certificates=[]
for j in range(8):
    gaps=[q_end[j],sub(z_end[j],q_end[j]),sub(y,z_end[j])]
    for i,g in enumerate(gaps):
        if g == L():
            continue
        vals=[norm(g,Q('1/4')),norm(g,Q(1))]
        assert min(vals)>=0 and max(vals)>0,(j,i,g,vals)
        endpoint_certificates.append({'section':j,'gap':i+1,'ends':list(map(str,vals))})
for j,g in enumerate(durations):
    vals=[norm(g,Q('1/4')),norm(g,Q(1))]
    assert min(vals)>=0 and max(vals)>0,(j,g,vals)
    endpoint_certificates.append({'duration':j+1,'ends':list(map(str,vals))})
equal('first failure difference',sub(times[5],times[4]),L(2,'-1/2'))
J=[[Q('-2/3'),Q('5/6')],[Q(0),Q(1)]]
Ji=[[Q('-3/2'),Q('5/4')],[Q(0),Q(1)]]
equal('J inverse',matmul(J,Ji),[[Q(1),Q(0)],[Q(0),Q(1)]])
equal('fixed standard center',norm(F,Q('1/2')),Q('1/2'))
ratios=list(map(Q,['1','2/3','3/2','1/4','4','2/3','1']))
equal('odd parity and speed product',-reduce(lambda a,b:a*b,ratios,Q(1)),Q('-2/3'))
equal('centered duration D coefficient',Q('23/9')/3+Q('5/3')*Q('2/3'),Q('53/27'))
# New corollary: exact infinite kernel on r=x/y and its rational clock.
rho=Q('-2/3')
def f(r): return Q('5/6')+rho*r
equal('kernel left endpoint maps to 2/3',f(Q('1/4')),Q('2/3'))
equal('kernel right endpoint maps to 1/4',f(Q('7/8')),Q('1/4'))
equal('fixed ratio',f(Q('1/2')),Q('1/2'))
# f is decreasing, so these endpoint identities prove strict invariance.
assert Q('1/4')<Q('2/3')<Q('7/8')
# Each coefficient is checked algebraically for N=0 and the arbitrary-N
# increment. A formal symbol r^N is represented by its coefficient pair.
equal('time sum baseline',Q('23/9')/2+Q('5/3'),Q('53/18'))
equal('time sum oscillating increment',Q('23/15')*(1-rho),Q('23/9'))
# Gap linear forms and SOS witnesses are identically 4x-y and 7y-8x.
equal('first gap witness',sub(mul(3,x),sub(y,x)),L(4,-1))
equal('second gap witness',sub(mul(7,sub(y,x)),x),L(-8,7))
report={'status':'PASS','checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'checked_equalities':checks,'whole_interval_certificates':endpoint_certificates,'scope':'Static rational affine identities only; no source imports, collision selection, trajectory stepping, old checker execution, or formal-assistant proof.'}
(OUT/'static_identity_receipt.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':'PASS','equalities':len(checks),'whole_interval_certificates':len(endpoint_certificates)}))

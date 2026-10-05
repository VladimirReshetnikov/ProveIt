"""Independent Gaussian integration-by-parts recurrence, with direct binomial jets."""
from functools import lru_cache
from pathlib import Path
import json,sympy as s
m=s.symbols('m',positive=True)
@lru_cache(None)
def moment(powers):
    powers=tuple(sorted(powers))
    if 1 in powers:return s.Integer(0)
    zeros=powers.count(0)
    if zeros:return s.factor(m**zeros*moment(tuple(x for x in powers if x)))
    if not powers:return s.Integer(1)
    ell=powers[-1];rest=list(powers[:-1]);v=0
    for a in range(ell-1):v+=moment(tuple(sorted(rest+[a,ell-2-a])))
    v-=s.Rational(ell-1,1)*moment(tuple(sorted(rest+[ell-2])))/m
    for index,j in enumerate(rest):
        others=rest[:index]+rest[index+1:]
        v+=j*(moment(tuple(sorted(others+[ell+j-2])))-moment(tuple(sorted(others+[ell-1,j-1])))/m)
    return s.factor(v/4)
e,y=s.symbols('e y');x=e*y
entropy=((s.Rational(1,2)+x)*s.log(1+2*x)+(s.Rational(1,2)-x)*s.log(1-2*x))
log_binomial=-entropy/e**2+2*y*y-s.log(1-4*e*e*y*y)/2+e*e/s.Integer(12)*(1-4/(1-4*e*e*y*y))
series=s.series(log_binomial,e,0,6).removeO().expand()
S2,S4,S6=s.symbols('S2 S4 S6')
P1=s.expand(series.coeff(e,2));P2=s.expand(series.coeff(e,4))
def sum_coordinates(p):
    d=s.Poly(p,y);out=0
    for (k,),v in d.terms():out+=v*{0:m,2:S2,4:S4,6:S6}[k]
    return s.expand(out)
L1=sum_coordinates(P1)+(m-2)*S2+(4/m-m)/12
L2=sum_coordinates(P2)+((m-8)*S4+3*S2*S2)/2

def expectation(poly):
    out=0
    for powers,v in s.Poly(s.expand(poly),S2,S4,S6).terms():
        traces=(2,)*powers[0]+(4,)*powers[1]+(6,)*powers[2]
        out+=v*moment(traces)
    return s.factor(out)
c1=expectation(L1);c2=expectation(L2+L1*L1/2)
expected1=(m*m-1)**2/(12*m);expected2=(m*m-1)*(m**6+3*m*m-1)/(288*m*m)
if s.factor(c1-expected1)!=0 or s.factor(c2-expected2)!=0:raise RuntimeError('coefficient mismatch')
# Independent exact g(3,n) recurrence of Sun: g(n+1)+g(n)=R(n).
t=s.symbols('t');cm1=c1.subs(m,3);cm2=c2.subs(m,3)
lhs=s.series((27*(1+t)**(-4)*(1+cm1*t/(1+t)+cm2*t*t/(1+t)**2)+1+cm1*t+cm2*t*t)/28,t,0,3).removeO()
# R(n)=(3n)!/(n!)^3*(7n+1)/(2(n+1)^2(4n^2-1)).
rhs=s.series((1-s.Rational(2,9)*t+s.Rational(2,81)*t*t)*(1+t/7)*(1+t)**(-2)/(1-t*t/4),t,0,3).removeO()
if s.expand(lhs-rhs)!=0:raise RuntimeError('Sun height3 check')
out={'passed':True,'method':'trace-zero eigenvalue integration by parts; no Wick pairings','binomial_log_jets':[str(P1),str(P2)],'L1':str(s.factor(L1)),'L2':str(s.factor(L2)),'moments':{str(p):str(moment(p)) for p in ((2,),(4,),(6,),(2,2),(2,4),(4,4),(3,3))},'c1':str(c1),'c2':str(c2),'Sun_height3_recurrence_check':True}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

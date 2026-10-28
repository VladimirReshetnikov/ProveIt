"""Author-written arithmetic check. Does not import or execute archive programs."""
from fractions import Fraction as F
from math import isqrt, log2, pi, sqrt, log
import json

def require(c,m):
    if not c: raise ArithmeticError(m)
def sqrt_interval(x,D=10**30):
    q=isqrt(x.numerator*D*D//x.denominator)
    return F(q,D), F(q+1,D)
def atan_interval(inv,n=60):
    x=F(1,inv)
    ss=sum(((-1)**k*x**(2*k+1)/F(2*k+1) for k in range(n)),F(0))
    nxt=x**(2*n+1)/F(2*n+1)
    return (ss,ss+nxt) if n%2==0 else (ss-nxt,ss)
a,b=atan_interval(5);c,d=atan_interval(239)
pl,pu=16*a-4*d,16*b-4*c
N=60
ll=2*sum((F(1,(2*k+1)*3**(2*k+1)) for k in range(N)),F(0))
lu=ll+F(9,4*(2*N+1)*3**(2*N+1))
klo=pl*sqrt_interval(F(2))[0]/lu
khi=pu*sqrt_interval(F(2))[1]/ll
# Imported matrix-support certificate from independent teammate; arithmetic only here.
bsq=F(27980397750833,82810000000000)
alpha2=F(24,169); A=F(119,1000); q=F(24,125); f0=A*(1-q)
require(338**119<2**1000,'low-degree strict packing')
require(q>F(1,6) and F(2,13)<F(1,6),'depth/taper bootstrap')
bl,bh=sqrt_interval(bsq);al,ah=sqrt_interval(alpha2);ql,qh=sqrt_interval(q)
require(ah/(1-F(2,13)/ql)<bl,'paid infinite child term below local term')
fl,fh=sqrt_interval(f0)
cl=klo*bl/fh;ch=khi*bh/fl
require(ch<F(12016,1000),'safe eventual 12.016 coefficient')
# Flags at arities 16,8,4; existing fixed trees at 6,5.
rs=[16,16,8,6,5]
fs=[F(12499,10**6),F(12499,10**6),F(2083,250000),F(107,20000),F(219,50000)]
bs=[F((r-1)*(4*r+10),9*r*r) if r in [4,8,16] else F({6:24,5:18}[r],r*r) for r in rs]
m=F(1);sl=sh=F(0);cum=F(0);levels=[]
for r,f,b2 in zip(rs,fs,bs):
    cum+=f
    # Generic root/later capacity uses rational upper bound on log2 r.
    lr={16:F(4),8:F(3),6:F(517,200),5:F(1161,500)}[r]
    require(F(9,10)+(2 if not levels else 1)*cum*lr<1,'generic strict gate')
    el,eh=sqrt_interval(b2/f);sl+=m*el;sh+=m*eh
    levels.append({'r':r,'f':str(f),'mass':str(m),'b2':str(b2)})
    m*=F(2,r)
require(6**200<2**517 and 5**500<2**1161,'log upper certificates')
f5=F(513,200000);qt=F(5,8);b4sq=F(13,24)
require(cum+f5/(1-qt)==F(499,10000),'cumulative tail budget')
require(F(9,10)+2*F(499,10000)<1,'tail strict gate')
tlo,thi=sqrt_interval(b4sq/f5);qtl,qth=sqrt_interval(qt)
sl+=m*tlo/(1-F(1,2)/qth);sh+=m*thi/(1-F(1,2)/qtl)
clp=klo*sl;chp=khi*sh
require(chp<F(46072,1000),'safe eventual polyspace46.072')
# Degree<=s^.51 polynomial-space specialization: flag-friendly prefix.
deg_rs=[16,16,8,6,5,4,4]
deg_As=[F(1531,25000),F(1111,10000),F(357,2500),F(81,500),F(1771,10000),F(1911,10000),F(1999,10000)]
dm=F(1);da=F(0);dsl=dsh=F(0);deg_levels=[]
for i,(r,Ai) in enumerate(zip(deg_rs,deg_As)):
    fi=Ai-da
    lr={16:F(4),8:F(3),6:F(517,200),5:F(1161,500),4:F(2)}[r]
    require(F(51,100)+(2 if i==0 else 1)*Ai*lr<1,'degree .51 retained gate')
    require(Ai*(1+2*lr)<1,'degree .51 rounding gate')
    b2=F((r-1)*(4*r+10),9*r*r) if r in [4,8,16] else F({6:24,5:18}[r],r*r)
    dl,dh=sqrt_interval(b2/fi);dsl+=dm*dl;dsh+=dm*dh
    deg_levels.append({'r':r,'A':str(Ai),'f':str(fi),'mass':str(dm),'b2':str(b2)})
    da=Ai;dm*=F(2,r)
dft=F(391,40000);dqt=F(3,4);dAt=da+dft/(1-dqt)
require(dAt==F(239,1000) and dm==F(1,7680),'degree .51 tail identities')
require(3**200<2**317,'tail log bound')
require(dAt*(1+2*F(317,200))<1,'degree .51 tail rounding')
require(F(51,100)+dAt*F(317,200)<1,'degree .51 tail retained')
require(dAt<F(51,100),'new degrees under old degree cap')
dl,dh=sqrt_interval(F(2,3)/dft);dql,dqh=sqrt_interval(dqt)
dsl+=dm*dl/(1-F(2,3)/dqh);dsh+=dm*dh/(1-F(2,3)/dql)
dcl=klo*dsl;dch=khi*dsh
require(dch<F(2114,100),'degree .51 safe eventual21.14')
require(dcl>21,'negative degree .51 coefficient')
res={'scope':'Arithmetic certificates only; inherited identities, flag lemma and independently certified rectangular tree support are imports. No archive code execution.',
'lowdegree':{'r':13,'root_degree_exponent':'1/12','A':str(A),'q':str(q),'f0':str(f0),'b_squared':str(bsq),'time_space_interval':[str(cl),str(ch)],'decimal_display':[float(cl),float(ch)],'safe_eventual':'12.016'},
'generic_polyspace':{'levels':levels,'tail_r':4,'tail_f':str(f5),'tail_q':str(qt),'time_interval':[str(clp),str(chp)],'decimal_display':[float(clp),float(chp)],'safe_eventual':'46.072'},'degree_051_polyspace':{'levels':deg_levels,'tail_r':3,'tail_f':str(dft),'tail_q':str(dqt),'time_interval':[str(dcl),str(dch)],'decimal_display':[float(dcl),float(dch)],'safe_eventual':'21.14'},'negative_controls':5}
# Explicit anti-regression controls: bad capacity, paid children, impossible bounds.
require(not(338**120<2**1000),'negative capacity control')
require(ah/(1-F(2,13)/sqrt_interval(F(1,10))[0])>bh,'negative child control')
require(cl>12,'negative claimed lowdegree coefficient')
require(clp>46,'negative claimed polyspace coefficient')
print(json.dumps(res,indent=2))

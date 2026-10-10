"""Focused fresh checks from independent mpmath definitions; no PSLQ oracle."""
from pathlib import Path
import json
import mpmath as mp

mp.mp.dps = 65
checks = []
def check(name, lhs, rhs, tol=mp.mpf('1e-48')):
    residual = abs(lhs-rhs)
    checks.append(dict(name=name, residual=mp.nstr(residual,12), tolerance=str(tol), passed=bool(residual<tol)))
    print(name, checks[-1]['passed'], mp.nstr(residual,6), flush=True)
def li(s,z): return mp.polylog(s,z)
def cl(s,x): return mp.im(li(s,mp.exp(mp.j*x))) if s%2==0 else mp.re(li(s,mp.exp(mp.j*x)))
pi=mp.pi; l2=mp.log(2); l3=mp.log(3); phi=(1+mp.sqrt(5))/2
check('corrected rational dilogarithm',6*li(2,mp.mpf(1)/3)-li(2,mp.mpf(1)/9),pi*pi/3-l3*l3)
check('Nielsen half',mp.quad(lambda x:mp.log(1-x)**2/x,[0,mp.mpf(1)/2])/2,mp.zeta(3)/8-l2**3/6)
check('Nielsen minus one',mp.quad(lambda x:mp.log(1+x)**2/x,[0,1])/2,mp.zeta(3)/8)
for q in (8,12,24):
    g=mp.catalan; v=cl(2,pi/3); w8=cl(2,pi/4); w24=cl(2,pi/12)
    pairs={8:[(3*pi/4,w8-g/2)],12:[(pi/6,2*g/3+v/4),(5*pi/6,2*g/3-v/4)],
           24:[(5*pi/12,(16*w8+24*w24-4*g-3*v)/24),(7*pi/12,(4*w8+6*w24-3*g)/6),(11*pi/12,(24*w24-8*g-3*v)/24)]}[q]
    for angle,rhs in pairs:check('Clausen distribution '+str(q)+' '+mp.nstr(angle,5),cl(2,angle),rhs)
def fdelta(p,q):
    aa=[mp.exp(2*pi*mp.j*j/p) for j in range(p)]
    def f(a,b):return li(2,b/(b-1))-li(2,(a-b)/(1-b))
    def inner(n):return mp.fsum(f(a,mp.exp(2*pi*mp.j*k/n)) for a in aa for k in range(1,n))
    return mp.re(inner(q)-inner(p))
for q in range(2,15):
    logs=mp.fsum(mp.log(2*mp.sin(pi*k/q))**2 for k in range(1,(q-1)//2+1))
    check('Herglotz F1/'+str(q),fdelta(1,q),-mp.mpf((q-1)*(3*q-2))/(24*q)*pi**2-logs-(l2*l2/2 if q%2==0 else 0))
    if q>=3:
        ds=mp.fsum(li(2,-mp.cot(pi*k/q)**2) for k in range(1,(q-1)//2+1))
        rhs=-mp.mpf((q-1)*(q-2))/(12*q)*pi**2+l2*l2-2*logs-ds/2-(l2*l2 if q%2==0 else 0)
        check('Herglotz F2/'+str(q),fdelta(2,q),rhs)
def w(q):return mp.fsum(mp.cot(2*pi*k/q)*cl(2,2*pi*k/q) for k in range(1,q) if (2*k)%q)
check('derived W12',w(12),11*mp.sqrt(3)*cl(2,pi/3)/9)
check('W8',w(8),mp.catalan)
def derivative_integral(x):
    def term(t):
        if not t:return mp.mpf(1)/(2*x)
        kernel=(mp.mpf(1)/2+t/12-t**3/720+t**5/30240) if t<mp.mpf('1e-12') else -1/mp.expm1(-t)-1/t
        return kernel*t/mp.expm1(x*t)
    return mp.quad(term,[0,1,5,20,mp.inf])
for q in (5,6,8,12):
    x=mp.mpf(2)/q
    check('Herglotz derivative integral q='+str(q),x*derivative_integral(x),1+(l2 if q%2 else 0)+mp.mpf(q*q-4)/(24*q)*pi*pi+w(q))
chi3=[0,1,-1]; chi4=[0,1,0,-1]
def L(s,c):return mp.fsum(c[k]*mp.zeta(s,mp.mpf(k)/len(c)) for k in range(1,len(c)))/mp.power(len(c),s)
for n in (1,2):
    for k in (1,2,3):
        # e_i of {1,1/2,...,1/k}; compare a parameter derivative to spectral jets.
        e=[mp.mpf(1)]+[mp.mpf(0)]*n
        for m in range(1,k+1):
            for i in range(n,0,-1):e[i]+=e[i-1]/m
        a=mp.mpf(2)/5
        rhs=(-1)**(n+k)*mp.factorial(k)*mp.factorial(n)*mp.fsum(e[n-j]*mp.diff(lambda s:mp.zeta(s,a),k+1,j)/mp.factorial(j) for j in range(n+1))
        check('harmonic master n='+str(n)+' k='+str(k),mp.diff(lambda z:mp.stieltjes(n,z),a,k),rhs,mp.mpf('1e-43'))
for c in (chi3,chi4):
    q=len(c)
    for k in (1,2,3):
        lp=lambda s:L(s,c)
        positive=mp.diff(lp,k+1)/lp(k+1)
        if k%2==0: negative=mp.diff(lp,-k)/lp(-k)
        else:negative=mp.diff(lp,-k,2)/(2*mp.diff(lp,-k))
        check('bridge conductor='+str(q)+' k='+str(k),positive+negative,mp.euler+mp.log(2*pi/q)-mp.harmonic(k))
zp=lambda s:mp.zeta(s,mp.mpf(1)/3)
g=mp.euler; lp=mp.log(2*pi); t=mp.mpf(1)/3
third_printed=pi**2/72-lp**2/3+l3**2/24-mp.mpf(2)/3*l3*lp-g/12*(4*g+8*lp-l3)+(g+mp.log(6*pi))*mp.loggamma(t)-mp.stieltjes(1)/2+mp.sqrt(3)/(12*pi)*(mp.stieltjes(2,t)-mp.stieltjes(2,2*t))
check('Stieltjes Gamma1 third printed corrected sign',mp.diff(zp,0,2)/2-mp.diff(mp.zeta,0,2)/2,third_printed)
check('negative polygamma quarter',mp.quad(lambda t:mp.loggamma(t),[0,mp.mpf(1)/4]),
      mp.mpf(3)/32+l2/8+mp.log(pi)/8+mp.catalan/(4*pi)-mp.mpf(9)/8*mp.diff(mp.zeta,-1))
alpha1=mp.findroot(lambda x:x**3-2*x*x-3*x+1,(-2,-1))
alpha3=mp.findroot(lambda x:x**3-2*x*x-3*x+1,(2,3))
reg=abs(mp.log(-alpha1)*mp.log(3-alpha3)-mp.log(3-alpha1)*mp.log(alpha3))
u=16+mp.sqrt(257)
jcal=mp.quad(lambda t:mp.log1p(t**u)/(1+t),[0,1])-l2*l2/2+pi*pi/24*(u-1/u)
check('Stark numerical candidate signed cubic determinant',jcal,4*mp.zeta(2)+l2*mp.log(u)+2*reg)
# Large golden ladders: direct substitution is independent of their PSLQ origin.
ell=mp.log(phi)
ladder_data=[
 (5,{2:4455,4:-1215,6:-360,12:15},3015*mp.zeta(5)-702*ell**5+180*pi**2*ell**3-38*pi**4*ell),
 (5,{2:45000,4:-16875,10:-144,20:9},28944*mp.zeta(5)-6000*ell**5+1600*pi**2*ell**3-356*pi**4*ell),
 (5,{2:15660,4:-19440,6:7680,8:2430,24:-15},5025*mp.zeta(5)+2088*ell**5-240*pi**2*ell**3-28*pi**4*ell),
 (6,{2:98820,4:-104490,6:33120,8:7290,12:-50,24:-15},-13032*ell**6+3240*pi**2*ell**4-424*pi**4*ell**2+32155*mp.zeta(6)),
 (7,{2:74707920,4:-39497220,6:8346240,8:1377810,12:-6300,24:-945},2814912*ell**7-979776*pi**2*ell**5+213696*pi**4*ell**3-51448*pi**6*ell+44689995*mp.zeta(7)),
 (8,{2:-490795200,4:636131475,6:-388684800,8:82668600,10:9507456,12:5250000,20:-74277,24:-18900},-23641920*ell**8+7956480*pi**2*ell**6-1434720*pi**4*ell**4+184432*pi**6*ell**2-148565886*mp.zeta(8)),
 (9,{2:220857840000,4:-143129581875,6:58302720000,8:-9300217500,10:-855671040,12:-393750000,20:3342465,24:708750},-2364192000*ell**9+1022976000*pi**2*ell**7-258249600*pi**4*ell**5+55329600*pi**6*ell**3-14149132*pi**8*ell+125596001790*mp.zeta(9))]
for i,(weight,coef,rhs) in enumerate(ladder_data):
    check('golden ladder '+str(i+1)+' weight '+str(weight),mp.fsum(c*li(weight,phi**(-k)) for k,c in coef.items()),rhs)
def gen(a,b):
    return mp.im(mp.j*mp.quad(lambda x:(-mp.log(x))**(a-1)*li(b,mp.j*x)/(1-mp.j*x),[0,1])/mp.factorial(a-1))
beta=lambda k:mp.im(li(k,mp.j))
g6=[
 (5,1,2048,-64*pi**3*mp.zeta(3)-527*pi*mp.zeta(5)+4096*beta(6)),
 (4,2,1536,96*pi**3*mp.zeta(3)-32*pi**2*beta(4)+1581*pi*mp.zeta(5)-8448*beta(6)),
 (3,3,1024,-3*pi**3*mp.zeta(3)+64*pi**2*beta(4)-1581*pi*mp.zeta(5)+4608*beta(6)),
 (2,4,23040,-14*pi**4*mp.catalan+135*pi**3*mp.zeta(3)-1440*pi**2*beta(4)+23715*pi*mp.zeta(5)-69120*beta(6)),
 (1,5,92160,-150*pi**5*l2+56*pi**4*mp.catalan-270*pi**3*mp.zeta(3)+1920*pi**2*beta(4)-675*pi*mp.zeta(5))]
for a,b,m,rhs in g6:check('Gaussian double integral g'+str(a)+str(b),m*gen(a,b),rhs)
result=dict(engine='mpmath '+mp.__version__,working_precision=mp.mp.dps,checks=checks,all_pass=all(c['passed'] for c in checks))
Path(__file__).with_name('mpmath-results.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
raise SystemExit(0 if result['all_pass'] else 1)

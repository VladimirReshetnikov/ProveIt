"""Independent quadrature and exact algebra for the new logarithmic collision layer."""
import mpmath as mp
import sympy as sp
import json
from pathlib import Path
mp.mp.dps=70
z=mp.zeta(2)
def direct_U(b,a):
    if a==b==0: return mp.mpf(0)
    if b==0:
        lower=mp.quad(lambda y:mp.log1p(y/a)/y,[0,1])
    else:
        lower=mp.quad(lambda y:mp.log(y+a)/(y+b),[0,1])
    tail=mp.quad(lambda t:(mp.log1p(a*t)+b*t*mp.log(t))/(t*(1+b*t)),[0,1])
    return lower+tail

def closed_U(b,a):
    if a==b==0: return mp.mpf(0)
    if b==0: return z+mp.log(a)**2/2
    if a==0: return -z-mp.log(b)**2/2
    if a==b: return -mp.log(a)**2/2
    if a>b:
        d=a-b
        return mp.log(d)**2/2+z-mp.log(d)*mp.log(b)+mp.polylog(2,-b/d)
    d=b-a
    return -mp.log(d)**2/2-z-mp.log(a)*mp.log(b/d)-mp.polylog(2,-a/d)
checks=[]
for aa,bb in [('0','0'),('1.3','0'),('0','2.7'),('1.6','1.6'),('2.3','.7'),('.7','2.3'),('5.1','2.2'),('2.2','5.1')]:
    a,b=mp.mpf(aa),mp.mpf(bb)
    v1,v2=direct_U(b,a),closed_U(b,a)
    checks.append({'a':aa,'b':bb,'direct':mp.nstr(v1,60),'closed':mp.nstr(v2,60),'residual':mp.nstr(v1-v2,15)})
    assert abs(v1-v2)<mp.mpf('1e-65')

# Exact coefficient extraction with algebraically independent symbols.
e,L,l,g,g1,z2,z2p=sp.symbols('e L ell gamma gamma1 zeta2 zeta2prime')
beta=z2+z2p
h=lambda a:g-z2*a*e
k=lambda a:g1+beta*a*e
B=lambda X:z2+X**2/2
A0=L**2/4-l*L/2+z2/2-l**2/4
A1=L**2/2-l*L/2+z2/4
A2=L**2/2
T0=A0/e**2+h(1)/e*B(L)+h(-1)/(2*e)*B(L+l)+k(-2)/e*L
T1=A1/e**2+h(2)/e*B(L)+h(1)/(2*e)*L**2+k(-1)/(2*e)*(L+l)+h(-2)/e*B(L)
T2=A2/e**2+k(1)/e*L+h(1)/(2*e)*B(L+l)+h(-1)/(4*e)*(L+l)**2+h(-1)/e*B(L)+h(-2)/(2*e)*L**2
expected=[-z2**2/2+z2*l**2/4,-beta*l/2,z2**2/2]
exact=[]
for j,T in enumerate([T0,T1,T2]):
    const=sp.expand(T).coeff(e,0).coeff(L,0)
    residue=sp.simplify(const-expected[j])
    assert residue==0
    exact.append({'placement':j,'constant':str(const),'residual':str(residue),'epsilon_zero_log_polynomial':str(sp.expand(T).coeff(e,0))})
# All-pole identities checked directly from the kernel table at epsilon=e.
# Lower y=0, partial fractions (1/2,-1,1/2)/e^2.
UU=[
 [0,-z2-L**2/2,-z2-(L+l)**2/2],
 [z2+L**2/2,-L**2/2,-L**2/2-l*L-z2/2],
 [z2+(L+l)**2/2,-L**2/2+z2/2,-(L+l)**2/2]
]
for row,expectedA in zip(UU,[A0,A1,A2]):
    assert sp.expand(row[0]/2-row[1]+row[2]/2-expectedA)==0
record={'working_dps':mp.mp.dps,'universal_kernel_checks':checks,'exact_constant_checks':exact,'all_pole_checks':'3/3 exact zero','max_kernel_residual':mp.nstr(max(abs(mp.mpf(c['residual'])) for c in checks),15)}
Path(__file__).with_suffix('.json').write_text(json.dumps(record,indent=2))
print(json.dumps({'kernel_checks':len(checks),'max_residual':record['max_kernel_residual'],'exact_constant_checks':len(exact),'all_pole_checks':record['all_pole_checks']},indent=2))

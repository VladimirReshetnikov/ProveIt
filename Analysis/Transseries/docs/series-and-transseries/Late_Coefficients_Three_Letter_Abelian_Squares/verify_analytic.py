#!/usr/bin/env python3
"""Numerical analytic cross-checks; exact proof is in honeycomb_late_coefficients.tex."""
from pathlib import Path
import json,mpmath as m
from verify import recurrence,log_multiplier
D=Path(__file__).resolve().parent
m.mp.dps=70
L=m.log(9); C=1/(m.pi*m.sqrt(3)); C0=3*m.sqrt(3)/(4*m.pi)
F=lambda z:2*m.ellipk(z)/m.pi

def radial(x,delta):
    # Preserve the cubic complement near x=1; ellipk(1-w) would round to infinity.
    if x==0 or delta==0:return m.mpf(0)
    w=delta**3*(x+3)/(16*x)
    z=1-w
    f=1/m.agm(1,m.sqrt(w)) if delta>0 else 1/(m.sqrt(z)*m.agm(1,m.sqrt(-w/z)))
    return m.sqrt(x)*f/(2*m.pi)

def moment(s):
    left=m.quad(lambda r:(1-r)**(2*s)*radial(1-r,-r),[0,1])
    right=m.quad(lambda r:2*(1+2*r)**(2*s)*radial(1+2*r,2*r),[0,1])
    return left+right
def Gminus(v):
    x=m.exp(-v/2); w=(x-1)**3*(x+3)/(16*x)
    return m.exp(-3*v/4)*F(w)
def J(s):return s*m.quad(lambda v:m.exp(-s*v)*Gminus(v),[0,1,m.inf])
rows=[]
M=[1,3]
for n in range(1,31):M.append(((10*n*n+10*n+3)*M[-1]-9*n*n*M[-2])//((n+1)**2))
for n in [1,2,5,10,20]:
    z=moment(n)
    assert abs(z/M[n]-1)<m.mpf('1e-50'), (n,z)
    jj=J(n)
    assert 0<jj<1, ('Stokes integral sanity',n,jj)
    j4=1-m.mpf(3)/(4*n)+m.mpf(9)/(16*n*n)-m.mpf(15)/(32*n**3)
    if n>=5:
        assert abs(jj-j4)<m.mpf(1)/n**4, ('Stokes four-term sanity',n,jj-j4)
    rows.append({'N':n,'moment_relative_error':m.nstr(z/M[n]-1,12),'J':m.nstr(jj,35),
                 'J_four_term_error':m.nstr(jj-j4,20),
                 'J_four_term_bound_asserted':n>=5})
a=recurrence(500); inv=[]
for n in [20,80,200,500]:
    Y=m.log(m.mpf(a[n])/(C*m.sqrt(2*m.pi)))
    t=Y/m.lambertw((4/L)*Y/m.e);h=m.log((4/L)*t);b=m.log(t)/(2*h);c1=m.mpf(1)/12-3*L/4
    est=t+b+(b/2-b*b/2-c1)/(t*h)
    assert abs(est-n)<m.mpf(2)/n**2, ('late index inverse sanity',n,est-n)
    inv.append({'n':n,'estimate':m.nstr(est,40),'error':m.nstr(est-n,20)})
orig=[]
for n in [10,20,30]:
    y=M[n];t=-m.lambertw(-C0*L/y,-1)/L
    est=t+1/(4*L*t)+(1/(4*L**2)-1/(32*L))/t**2
    assert abs(est-n)<m.mpf('0.1')/n**3, ('original moment inverse sanity',n,est-n)
    orig.append({'n':n,'estimate':m.nstr(est,35),'error':m.nstr(est-n,20)})
r={'assertion_scope':'Finite consistency checks: density relative error <1e-50; 0<J<1; J four-term error <N^-4 for N>=5; late-index inverse error <2/n^2; original-moment inverse error <0.1/n^3. Inverse-sector family (36c-h) is not numerically tested.', 'moment_density_checks':rows,'late_index_inverse_checks':inv,'original_moment_inverse_checks':orig}
# ed. (2026-10-02): newline='\n' so the file is LF on Windows too (as delivered,
# the platform's line endings). It is written beside this script; run it on a copy.
(D/'analytic_verification.json').write_text(json.dumps(r,indent=2)+'\n',newline='\n')
print(json.dumps(r,indent=2))

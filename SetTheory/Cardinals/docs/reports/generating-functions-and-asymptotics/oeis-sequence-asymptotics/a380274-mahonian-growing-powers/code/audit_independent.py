"""Independent Hermite-polynomial and odd-n Mahonian verification.

Uses density Edgeworth polynomials rather than the original weighted-Fourier
moment script. Numerical references use exact integer coefficient recurrence.
All emitted files are next to this script.
"""
from pathlib import Path
import hashlib
import json
import sympy as S
import mpmath as mp

ROOT = Path(__file__).resolve().parent
z, n, y, t, j = S.symbols('z n y t j')
K = 5
V = n*(n-1)*(2*n+5)/72
lam = {m: S.series(S.bernoulli(2*m)/(2*m)*S.summation(j**(2*m)-1,(j,1,n))/V**m,n,S.oo,K+1).removeO().subs(n,1/z).expand() for m in range(2,K+2)}
L = sum(lam[m]*t**(2*m)/S.factorial(2*m) for m in lam)
expL = S.Integer(1)
term = S.Integer(1)
for k in range(1,K+1):
    poly = S.Poly(S.expand(term*L),z)
    term = sum(c*z**p[0] for p,c in poly.terms() if p[0]<=K)/k
    expL += term
polys = []
for k in range(K+1):
    poly = S.Poly(S.expand(expL).coeff(z,k),t)
    polys.append(S.expand(sum(c*S.hermite_prob(p[0],y) for p,c in poly.terms())))
# f is the Edgeworth correction multiplying exp(-y*y/2).
f = sum(sum(p.coeff(y,h)*y**h for h in (0,2,4))*z**k for k,p in enumerate(polys))
f0 = f.subs(y,0)
f2 = S.diff(f,y,2).subs(y,0)
f4 = S.diff(f,y,4).subs(y,0)
a = S.series(1-f2/f0,z,0,K+1).removeO()
b = S.series(f4/f0-3*(f2/f0)**2,z,0,K+1).removeO()
logJ = S.series(S.log(f0),z,0,4)
unnorm = S.series((V.subs(n,1/z)*logJ.removeO()).expand(),z,0,1)
expected = [S.Integer(1),-S.Rational(27,25),S.Rational(21087,61250),-S.Rational(19894023,3062500),S.Rational(18889730796483,907878125000)]
assert all(S.expand(a).coeff(z,k)==expected[k] for k in range(5))
assert S.expand(b).coeff(z,1)==-S.Rational(54,25)
symbolic = {'a_through_n5':str(a),'b_through_n5':str(b),'J0_through_n5':str(f0),'logJ0_through_n3':str(logJ),'V_logJ0_through_constant':str(unnorm)}

mp.mp.dps = 85
def asmp(v):
    return mp.mpf(str(S.numer(v)))/mp.mpf(str(S.denom(v)))
ac = [asmp(S.expand(a).coeff(z,k)) for k in range(6)]
ell = [mp.mpf(0)]+[asmp(S.expand(S.series(S.log(f0),z,0,5).removeO()).coeff(z,k)) for k in range(1,5)]
q4 = -mp.mpf(81)/25
q5 = mp.mpf(3)/2*(asmp(S.expand(b).coeff(z,2))+mp.mpf(81)/25)
rows = []
row = [1]
targets = {21,23,61,63,121,123,241,243,481,483}
for ni in range(1,max(targets)+1):
    out = []
    accum = 0
    for k in range(len(row)+ni-1):
        if k<len(row): accum += row[k]
        if k>=ni: accum -= row[k-ni]
        out.append(accum)
    row = out
    if ni not in targets: continue
    center = (len(row)-1)//2
    delta = mp.mpf((len(row)-1)%2)/2
    vn = mp.mpf(ni*(ni-1)*(2*ni+5))/72
    a4 = sum(ac[k]/mp.mpf(ni)**k for k in range(5))
    for rho in [mp.mpf('0.2'),mp.mpf(1),mp.mpf(5)]:
        th = mp.mpf(0); approx = mp.mpf(0)
        phi2 = mp.mpf(0); phi4 = mp.mpf(0); phi24 = mp.mpf(0)
        for m in range(80):
            x = mp.mpf(m)+delta
            mult = 1 if x==0 else 2
            D2 = x*x-delta*delta; D4 = x**4-delta**4
            weight = mult*mp.exp(-rho*D2/2)
            th += weight; phi2 += D2*weight; phi4 += D4*weight; phi24 += D2*D4*weight
            approx += mult*mp.exp(-rho*a4*D2/2)+q4*rho*D4*weight/ni**4
        exact = mp.mpf(0); tail = mp.mpf(0)
        for m in range(center+1):
            x = mp.mpf(m)+delta
            term = (1 if x==0 else 2)*mp.exp(rho*vn*mp.log(mp.mpf(row[center-m])/row[center]))
            exact += term
            if m>5 and m<center:
                next_ratio_power = mp.exp(rho*vn*mp.log(mp.mpf(row[center-m-1])/row[center-m]))
                tail = term*next_ratio_power/(1-next_ratio_power)
                if tail<mp.mpf('1e-75'): break
        prediction = (-rho*ac[5]*phi2/2+q5*rho*phi4+q4*(-rho*ac[1]/2)*rho*phi24)/th
        log_sum = rho*vn*mp.log(row[center])+mp.log(exact)
        xx = ((144*log_sum/rho)/mp.lambertw((144*log_sum/rho)*mp.exp(-4)))**(mp.mpf(1)/4)
        BB = (mp.log(xx)+2*mp.log(6)-3)/(2*(4*mp.log(xx)-3))
        inversion_error = ni-xx+BB
        Zdelta = th*mp.exp(-rho*delta*delta/2)
        def forward_L0(x):
            vx=x*(x-1)*(2*x+5)/72
            return rho*vx*(mp.loggamma(x+1)-mp.log(2*mp.pi*vx)/2+sum(ell[k]/x**k for k in range(1,4)))+mp.log(Zdelta)
        root_L0=mp.findroot(lambda x:forward_L0(x)-log_sum,(mp.mpf(ni)-mp.mpf('0.01'),mp.mpf(ni)+mp.mpf('0.01')))
        root_error=root_L0-ni
        root_scaled=root_error*ni**4*mp.log(ni)
        root_prediction=ell[4]/4+mp.mpf(243)/50*(phi2/th+delta*delta)
        rec = {'L0_root_error':mp.nstr(root_error,30),'L0_n4_logn_scaled_error':mp.nstr(root_scaled,30),'L0_predicted_scaled_limit':mp.nstr(root_prediction,30),'log_S':mp.nstr(log_sum,50),'inversion_X':mp.nstr(xx,40),'inversion_corrected_error':mp.nstr(inversion_error,30),'n_times_inversion_corrected_error':mp.nstr(ni*inversion_error,30),'n':ni,'delta':str(delta),'rho':str(rho),'exact_T':mp.nstr(exact,50),'exact_tail_upper_bound':mp.nstr(tail,8),'relative_refined_error':mp.nstr(exact/approx-1,30),'n5_relative_error':mp.nstr(ni**5*(exact/approx-1),30),'predicted_n5_limit':mp.nstr(prediction,30)}
        rows.append(rec)
        if rho==1: print(ni, str(delta), rec['n5_relative_error'], rec['predicted_n5_limit'], flush=True)
result = {'method':'Hermite density expansion plus independent exact integer recurrence','precision_digits':mp.mp.dps,'symbolic':symbolic,'numerics':rows,'audited_tex_sha256':hashlib.sha256((ROOT/'mahonian_crossover.tex').read_bytes()).hexdigest()}
(ROOT/'audit_independent_results.json').write_text(json.dumps(result,indent=2)+'\n')
(ROOT/'audit_symbolic.txt').write_text('\n'.join(k+' = '+v for k,v in symbolic.items())+'\n')
print('Wrote audit_independent_results.json and audit_symbolic.txt')

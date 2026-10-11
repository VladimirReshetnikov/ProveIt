"""Independent evaluation of the extra cubic Tornheim coordinate.
The proof is in Section 4.5 of the accompanying article.  These diagnostics use ordinary
high-precision arithmetic and do not claim interval certification.
"""
import json
from pathlib import Path
import mpmath as m


def evaluate(dps=60, N=60, M=180):
    m.mp.dps=dps
    g=m.euler; L=m.log(2*m.pi); z2=m.zeta(2); z3=m.zeta(3)
    deriv2=[m.diff(m.zeta, -k, 2) for k in range(N+1)]
    qs=[(-1)**k*deriv2[k]/m.factorial(k) for k in range(N+1)]
    bs=[m.bernpoly(j,0)/m.factorial(j) for j in range(N+1)]
    # bernpoly(1,0)=-1/2, matching x/(exp(x)-1).
    lowerP=m.fsum(bs[j]*(2/m.mpf(j-2)**3-2*g/m.mpf(j-2)**2+(g*g+z2)/(j-2)) for j in range(3,N+1))
    lowerQ=m.fsum(m.fsum(qs[k]*bs[n-k] for k in range(n+1))/(n-1) for n in range(2,N+1))
    logsum=m.mpf(0); tail=m.mpf(0)
    for n in range(2,M+1):
        logsum += m.log(n-1)**2
        tail += logsum*m.e1(n)
    integral=lowerP+lowerQ+tail
    h20=g/4+m.mpf(3)/8-deriv2[0]/2+integral/2
    z30=m.diff(m.zeta,0,3); z3m=m.diff(m.zeta,-1,3)
    J=-12*h20-6*L*deriv2[0]-g**3/6-g*z2/2+3*g*deriv2[0]+6*g*deriv2[1]-z3/3-m.mpf(41)/2*z30+7*z3m
    kappa=J+m.mpf(35)/2*z30+6*L*deriv2[0]-9*z3m
    return {k:m.nstr(v,dps-8) for k,v in {'integral':integral,'h20':h20,'J':J,'kappa':kappa,'lower':lowerP+lowerQ,'tail':tail}.items()}

if __name__=='__main__':
    result={'parameters':{'dps':65,'N':70,'M':200},'values':evaluate(65,70,200),'error_status':'Uncertified high-precision diagnostics; truncation convergence checked separately.'}
    print(json.dumps(result,indent=2))
    Path(__file__).with_name('extra_coordinate_numerics.json').write_text(json.dumps(result,indent=2)+'\n')

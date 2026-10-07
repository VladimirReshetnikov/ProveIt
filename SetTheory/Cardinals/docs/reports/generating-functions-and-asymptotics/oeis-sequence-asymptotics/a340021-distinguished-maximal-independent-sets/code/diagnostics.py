"""High-precision numerical diagnostics, explicitly not error certificates."""
import json
import mpmath as mp

mp.mp.dps=220
a=mp.log(2)

def carriers(t,R=4, exact=False):
    L=mp.log(t,2)
    upper=max(30,int(2*L)+80)
    if exact:upper=min(upper,int(t))
    logs=[]; polys=[]; exactcor=[]
    for k in range(1,upper+1):
        y=t*mp.power(2,-k)
        logs.append(k*mp.log(t)-a*k*(k-1)/2-mp.loggamma(k+1)-y)
        C=[mp.mpf(0)]+[-mp.fsum(mp.mpf(i)**r for i in range(k))/r
                +k*y**r/r-y**(r+1)/(r+1) for r in range(1,R)]
        P=[mp.mpf(1)]
        for j in range(1,R):P.append(mp.fsum(r*C[r]*P[j-r] for r in range(1,j+1))/j)
        polys.append(P)
        if exact:
            exactcor.append(mp.fsum(mp.log1p(-mp.mpf(i)/t) for i in range(k))
                            +(t-k)*mp.log1p(-mp.power(2,-k))+y)
    peak=max(logs); weights=[mp.exp(q-peak) for q in logs]
    coeff=[mp.fsum(weights[k]*polys[k][j] for k in range(len(weights))) for j in range(R)]
    if exact:
        val=mp.fsum(weights[k]*mp.exp(exactcor[k]) for k in range(len(weights)))
        return peak,coeff,val,weights
    return peak,coeff,weights

def F(t,R):
    peak,c,w=carriers(t,R)
    H=mp.fsum(c[j]/t**j for j in range(R))
    return a*t*(t-1)/2-mp.loggamma(t+1)+peak+mp.log(H)

def show(x):return mp.nstr(x,35)

out={'label':'NONCERTIFIED NUMERICAL DIAGNOSTICS','algebraic_orders':[], 'switches':[], 'inverse':[]}
for n in [100,1000,10**6,10**12,10**24,10**40]:
    t=mp.mpf(n);peak,c,exact,w=carriers(t,4,True)
    approximations=[]
    for R in range(1,5):
        approx=mp.fsum(c[j]/t**j for j in range(R))
        err=approx/exact-1
        approximations.append({'R':R,'relative_error':show(err),'scaled_error':show(err*t**R/mp.log(t)**(2*R))})
    out['algebraic_orders'].append({'n':str(n),'approximations':approximations})
for k in [10,30,100,300]:
    W=mp.lambertw(mp.mpf(k+1)/2);nk=mp.power(2,k+1)*W
    for s in [-2,0,2]:
        # Direct inversion of y exp(y/2)/(k+1)=exp(s), avoiding a numerical root solve.
        t=mp.power(2,k+1)*mp.lambertw(mp.exp(s)*(k+1)/2)
        peak,c,w=carriers(t,1)
        total=c[0];pk=w[k-1]/total;pk1=w[k]/total
        out['switches'].append({'k':k,'s':s,'n':show(t),'P_k':show(pk),'P_k1':show(pk1),
            'outside':show(1-pk-pk1),'logistic_P_k1':show(mp.exp(s)/(1+mp.exp(s)))})
for n in [100,1000,10000,10**6]:
    t=mp.mpf(n);peak,c,exact,w=carriers(t,4,True)
    T=a*t*(t-1)/2-mp.loggamma(t+1)+peak+mp.log(exact)
    x=mp.sqrt(2*T/a);d=(mp.log(x)-1+a/2)/a;z=x+d
    row={'target_n':n,'target':'log identity Burnside count; unlabeled discrepancy omitted','errors':[show(z-t)]}
    for i in range(3):
        z=z-(F(z,4)-T)/mp.diff(lambda v:F(v,4),z)
        row['errors'].append(show(z-t))
    out['inverse'].append(row)
print(json.dumps(out,indent=2,sort_keys=True))

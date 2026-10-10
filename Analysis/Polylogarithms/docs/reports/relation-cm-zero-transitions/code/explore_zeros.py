import mpmath as mp
import json
mp.mp.dps = 60

def es(k,n):
    vals = [mp.mpf(1)] + [mp.mpf(0)]*n
    for j in range(1,k+1):
        for i in range(min(n,j),0,-1):
            vals[i] += vals[i-1]/j
    return vals

NMAX=30
ETAB=[es(k,NMAX) for k in range(80)]

def R(n,k,v):
    return mp.fsum(mp.factorial(n)/mp.factorial(n-i)*ETAB[k][i]*(-v)**(n-i)
                   for i in range(min(k,n)+1))

def value(n,a,k=1,M=24,Q=16):
    a=mp.mpf(a); A=a+M; p=k+1; v=mp.log(A)
    out = mp.fsum((a/(a+m))**p*R(n,k,mp.log(a+m)) for m in range(M))
    out += (a/A)**p*(A/k*R(n,k-1,v)+R(n,k,v)/2)
    for r in range(1,Q+1):
        out += (a/A)**p*mp.bernoulli(2*r)/mp.factorial(2*r)*mp.rf(k+1,2*r-1)/A**(2*r-1)*R(n,k+2*r-1,v)
    return out

if __name__=='__main__':
    result=[]
    for n in range(1,16):
        pts=[mp.mpf(j)/100 for j in range(30,351)]
        signs=[mp.sign(value(n,a)) for a in pts]
        brackets=[(str(pts[j]),str(pts[j+1])) for j in range(len(pts)-1) if signs[j]!=signs[j+1]]
        roots=[mp.findroot(lambda a:value(n,a), tuple(map(mp.mpf,bb))) for bb in brackets]
        row={'n':n,'roots':[mp.nstr(x,40) for x in roots]}
        result.append(row)
        print(json.dumps(row),flush=True)
    with open('agent_analytic/exploratory_roots.json','w') as fh:
        json.dump(result,fh,indent=2)

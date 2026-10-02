"""Exact and symbolic consistency checks. Python 3, mpmath, sympy."""
import json, math, hashlib
from pathlib import Path
import mpmath as mp
import sympy as sy
OUT=Path(__file__).resolve().parent
mp.mp.dps=70

def stirling_table(M,N):
    rows=[[1]+[0]*N]
    for m in range(1,M+1):
        old=rows[-1]
        rows.append([0]+[j*old[j]+old[j-1] for j in range(1,N+1)])
    return rows

def labelled_counts(k,N):
    L=[0]*(N+1)
    for n in range(1,N+1):
        L[n]=n**(k*n)-sum(math.comb(n-1,h-1)*n**(k*(n-h))*L[h] for h in range(1,n))
    assert all(L[n]%math.factorial(n-1)==0 for n in range(1,N+1))
    return [0]+[L[n]//math.factorial(n-1) for n in range(1,N+1)]

def suffix(k,n,h):
    r=n-h
    s=sum((-1)**j*math.comb(r,j)*(n-j)**(k*r) for j in range(r+1))
    assert s%math.factorial(r)==0
    return s//math.factorial(r)

def exhaustive_partition(k,n):
    # Enumerate restricted-growth words with final maximum n; count accessible ones.
    L=k*n+1
    total=accessible=0
    counts={h:0 for h in range(1,n)}
    def rec(word,mx,failed):
        nonlocal total,accessible
        if len(word)==L:
            if mx==n:
                total+=1
                if failed is None: accessible+=1
                else: counts[failed]+=1
            return
        for z in range(1,min(mx+1,n)+1):
            newmx=max(mx,z); ll=len(word)+1; ff=failed
            if (ll-1)%k==0:
                h=(ll-1)//k
                if 1<=h<n and newmx<=h and ff is None: ff=h
            rec(word+(z,),newmx,ff)
    rec((1,),1,None)
    return total,accessible,counts

results={'exact_renewal':[], 'exhaustive':[], 'large_n':{}, 'symbolic':{}}
for k in [2,3,4,5]:
    N=25; A=labelled_counts(k,N); S=stirling_table(k*N+1,N)
    for n in range(1,N+1):
        assert S[k*n+1][n]==A[n]+sum(A[h]*suffix(k,n,h) for h in range(1,n))
        if n>1: assert suffix(k,n,1)==S[k*n-k+1][n]
    results['exact_renewal'].append({'k':k,'through_n':N,'passed':True})
for k,n in [(2,2),(2,3),(3,2),(3,3)]:
    total,accessible,counts=exhaustive_partition(k,n)
    A=labelled_counts(k,n);S=stirling_table(k*n+1,n)
    assert total==S[k*n+1][n] and accessible==A[n]
    assert counts=={h:A[h]*suffix(k,n,h) for h in range(1,n)}
    results['exhaustive'].append({'k':k,'n':n,'partitions':total,'accessible':accessible,'first_failure_counts':counts})

k,v,z,u=sy.symbols('k v z u', positive=True)
c=1-k*(1-v)
D=lambda f:sy.expand(z*(sy.diff(f,z)-u*sy.diff(f,u)))
cums=[z/(1-u)]
for _ in range(3): cums.append(D(cums[-1]))
cums=[sy.factor(f.subs({z:k*v,u:1-v})) for f in cums]
K2,K3,K4=cums[1:]
tau=sy.factor(sy.Rational(13,12)/k-sy.Rational(1,12)-1/(2*K2)-K3/(2*K2**2)+K4/(8*K2**2)-5*K3**2/(24*K2**3))
Mom=[1/c]
for _ in range(3):Mom.append(sy.factor(-(1-v)*v/c*sy.diff(Mom[-1],v)))
d1=sy.factor(c*c*Mom[1]/2)
d2base=sy.factor(-c*c*(k*(k-1)*Mom[3]/24-(k+2)*Mom[2]/24+tau*Mom[1])-c*d1*Mom[1]/2)
assert sy.simplify(d1-k*(1-v)*v/(2*c))==0
results['symbolic']={'cumulants':list(map(str,cums)),'tau1':str(tau),'moments':list(map(str,Mom)), 'd1':str(d1), 'd2base':str(d2base)}
# Verify polynomial right-suffix coefficients against exact finite differences.
for kk in [2,3,4]:
    for r in range(1,8):
        for nn in [r+2,r+10,50]:
            gg=sy.series(((sy.exp(z)-1)/z)**r,z,0,(kk-1)*r+1).removeO()
            norm=sum((-1)**j*math.factorial((kk-1)*r)//math.factorial((kk-1)*r-j)*gg.coeff(z,j)*sy.Rational(1,nn)**j for j in range((kk-1)*r+1))
            assert sy.simplify(norm-sy.Rational(suffix(kk,nn,nn-r),math.comb(kk*r,r)*nn**((kk-1)*r)))==0
results['right_endpoint_exact_polynomial']='passed: k=2..4, r=1..7, three n values'

ft=sy.lambdify((k,v),tau,'mpmath'); fd2=sy.lambdify((k,v),d2base,'mpmath')
for kk in [2,3,4]:
    N=500; A=labelled_counts(kk,N)
    row=[1]+[0]*N; T={}
    for m in range(1,kk*N+2):
        row=[0]+[j*row[j]+row[j-1] for j in range(1,N+1)]
        if (m-1)%kk==0 and 1<=(m-1)//kk<=N:T[(m-1)//kk]=row[(m-1)//kk]
    vv=1+mp.lambertw(-kk*mp.exp(-kk))/kk;cc=1-kk*(1-vv)
    dd1=kk*(1-vv)*vv/(2*cc);dd2=fd2(kk,vv)-(cc*vv**2 if kk==2 else 0)
    tt=ft(kk,vv);q=(1-vv)*vv**(kk-1);beta=mp.exp(-(kk-1))/q;pref=1/(vv*mp.sqrt(2*mp.pi*cc))
    records=[]
    for n in [50,100,200,300,500]:
        b=mp.mpf(A[n])/T[n]
        TL=pref*beta**n*mp.mpf(n)**((kk-1)*n+mp.mpf('.5'))
        records.append({'n':n,'b':str(b),'n_times_first_residual':str(n*(b-cc)), 'n2_times_second_residual':str(n*n*(b-cc-dd1/n)), 'n3_after_d2':str(n**3*(b-cc-dd1/n-dd2/n**2)), 'n_times_T_correction':str(n*(mp.mpf(T[n])/TL-1))})
    results['large_n'][kk]={'c':str(cc),'d1':str(dd1),'d2':str(dd2),'tau1':str(tt),'rows':records}
    print(kk,'d1=',mp.nstr(dd1,18),'d2=',mp.nstr(dd2,18),'last n2=',records[-1]['n2_times_second_residual'],flush=True)
(OUT/'verification.json').write_text(json.dumps(results,indent=2)+'\n')
print('All exact and symbolic assertions passed. Wrote verification.json.',flush=True)

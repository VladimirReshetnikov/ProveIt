#!/usr/bin/env python3
"""Exact refined rows; independent labelled-word enumeration; saddle checks."""
import argparse,itertools,json,math,time
from pathlib import Path
import mpmath as mp
import sympy as s
from refined_coefficients import first_saddle,second_saddle

def exact_rows(N):
    S=[[0]*(N+1) for _ in range(N+1)];S[0][0]=1
    for n in range(1,N+1):
        for k in range(1,n+1):S[n][k]=S[n-1][k-1]+k*S[n-1][k]
    L=[[0]*(n//2+1) for n in range(N+1)];L[1][0]=1
    for n in range(2,N+1):
        for k in range(1,n//2+1):L[n][k]=math.factorial(k)*math.factorial(k-1)*sum(S[a][k]*S[n-a][k] for a in range(k,n-k+1))
    A=[[1]]
    for n in range(1,N+1):
        row=[0]*(n//2+1)
        for j in range(1,n+1):
            C=math.comb(n-1,j-1)
            for k,x in enumerate(L[j]):
                if x:
                    cx=C*x
                    for l,y in enumerate(A[n-j]):row[k+l]+=cx*y
        A.append(row)
    return A,L

def words(n):
    # Enumerate words literally using all label permutations and all color masks.
    # Conditions are checked independently of the integral or cumulants.
    out={}
    if n==0:return {(0,0):1}
    for colors in itertools.product((0,1),repeat=n-1):
        b=(0,)+colors;k=sum(b[i]==1 and b[i-1]==0 for i in range(1,n));j=0
        for x in b[::-1]:
            if x:break
            j+=1
        for p in itertools.permutations(range(1,n+1)):
            zmax=0;ok=True
            for i in range(n):
                if b[i]==0:
                    zmax=max(zmax,p[i])
                    if i and b[i-1]==0 and p[i]>p[i-1]:ok=False;break
                else:
                    if p[i]<=zmax or (i and b[i-1]==1 and p[i]<p[i-1]):ok=False;break
            if ok:out[k,j]=out.get((k,j),0)+1
    return out

def params(v):
    u=mp.exp(v);a=mp.exp(-v/2);r=2*mp.log1p(a);c=(mp.pi**2*a/(4*r))**(mp.mpf(1)/3)
    K=r/2-2-a;D=mp.exp(K)*mp.sqrt(c/(3*mp.pi));return r,c,D

def f(v):return -mp.log(params(v)[0])
def cfun(v):return params(v)[1]
def dfun(v):return mp.log(params(v)[2])
def coeffs(v,J=3):
    r,c,D=params(v);a=mp.exp(-v/2)
    g1=mp.pi*mp.sqrt(a)*(a*a-3)/(8*a)*mp.sqrt(r)
    g2=(4-a**3)/(6*a)*r
    g3=mp.pi*mp.sqrt(a)*(9*a**4+10*a*a-15)/(384*a*a)*r**mp.mpf('1.5')
    cs,gs,form=first_saddle(J)
    fun=s.lambdify((cs,*gs),form,'mpmath');aa=fun(c,*[g1,g2,g3][:J])
    bb=second_saddle(J);sub={s.Symbol('V',positive=True):mp.diff(f,v,2)}
    for j in range(1,J+1):
        sub[s.Symbol(f'A{j}_0')]=aa[j]
    # a_1 derivative needed at order3.
    if J>=3:
        def afun(w):
            rr,cc,_=params(w);ap=mp.exp(-w/2)
            return cc**2*(mp.mpf('.5')+rr*(ap*ap-3)/(4*ap))-5/(36*cc)
        sub[s.Symbol('A1_1')]=mp.diff(afun,v)
    for j in range(1,2*J+1):
        sub[s.Symbol(f'C{j}')]=mp.diff(cfun,v,j)
        sub[s.Symbol(f'D{j}')]=mp.diff(dfun,v,j)
    for j in range(3,2*J+7):sub[s.Symbol(f'F{j}')]=mp.diff(f,v,j)
    out=[]
    for b in bb:
        syms=sorted(b.free_symbols,key=str);out.append(s.lambdify(syms,b,'mpmath')(*[sub[z] for z in syms]))
    return aa,out

def main():
    p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=400);p.add_argument('--brute',type=int,default=8);args=p.parse_args();mp.mp.dps=70
    start=time.monotonic();A,L=exact_rows(args.n)
    out={'N':args.n,'initial_rows':A[:11],'independent_word_checks':[],'refined_asymptotics':[],'moment_checks':[],'singular_checks':[],'complex_coefficient_checks':[],'conditional_isolate_checks':[]}
    for n in range(args.brute+1):
        w=words(n);row=[sum(num for (k,j),num in w.items() if k==a) for a in range(n//2+1)]
        assert row==A[n]
        # e^-z H obtains counts with zero isolates, then binomial re-insertion.
        for k in range(n//2+1):
            for j in range(n+1):
                m=n-j
                bj=sum((-1)**h*math.comb(m,h)*(A[m-h][k] if k<len(A[m-h]) else 0) for h in range(m+1))
                assert w.get((k,j),0)==math.comb(n,j)*bj
        out['independent_word_checks'].append({'n':n,'total':sum(row),'joint_entries':len(w)})
    for n in [n for n in [40,80,120,160,200,240,320,400] if n<=args.n]:
        for al in ['0.2','0.3','0.4']:
            k=round(n*float(al));alpha=mp.mpf(k)/n
            v=mp.findroot(lambda v:mp.diff(f,v)-alpha,(-10,8))
            r,c,D=params(v);V=mp.diff(f,v,2);aa,bb=coeffs(v)
            lead=mp.factorial(n)*D*r**(-n)*mp.exp(-v*k+3*c*n**(mp.mpf(1)/3))*n**(-mp.mpf(4)/3)/mp.sqrt(2*mp.pi*V)
            delta=mp.mpf(n)**(-mp.mpf(1)/3);ratio=mp.mpf(A[n][k])/lead
            approx=[sum(bb[j]*delta**j for j in range(J+1)) for J in range(4)]
            jmean=mp.mpf(n)*A[n-1][k]/A[n][k]
            japprox=r-(r*c+3*mp.diff(cfun,v)*mp.diff(lambda x:params(x)[0],v)/V)*delta**2
            out['conditional_isolate_checks'].append({'n':n,'k':k,'mean':str(jmean),'approx_error':str(jmean-japprox),'scaled_error':str(n*(jmean-japprox))})
            out['refined_asymptotics'].append({'n':n,'k':k,'u':str(mp.exp(v)),'ratio':str(ratio),'errors':[str(ratio-x) for x in approx],'scaled_third_remainder':str((ratio-approx[3])/delta**4)})
        den=sum(A[n]);mean=mp.mpf(sum(k*x for k,x in enumerate(A[n])))/den
        var=mp.mpf(sum(k*k*x for k,x in enumerate(A[n])))/den-mean**2
        r,c,D=params(0);muapprox=n*mp.diff(f,0)+3*mp.diff(cfun,0)*n**(mp.mpf(1)/3)+mp.diff(dfun,0)
        varapprox=n*mp.diff(f,0,2)+3*mp.diff(cfun,0,2)*n**(mp.mpf(1)/3)+mp.diff(dfun,0,2)
        iso=mp.mpf(n)*sum(A[n-1])/den
        isoapprox=r-r*c*n**(-mp.mpf(2)/3)
        out['moment_checks'].append({'n':n,'mean':str(mean),'mean_approx_error':str(mean-muapprox),'variance':str(var),'variance_approx_error':str(var-varapprox),'isolate_mean':str(iso),'isolate_approx_error':str(iso-isoapprox)})
    for u in [mp.mpf('.25'),mp.mpf(1),mp.mpf(4),mp.mpc(1,.08)]:
        a=1/mp.sqrt(u);r=2*mp.log(1+a);K=r/2-2-a
        for w in [mp.mpf('0.01'),mp.mpf('0.002')]:
            z=r-w;logh=z+mp.quad(lambda x:u*z*(mp.exp(z)-mp.exp(z*x))/(1-u*mp.expm1(z*x)*mp.expm1(z*(1-x))),[0,.25,.5,.75,1])
            approx=mp.pi*mp.sqrt(a)/mp.sqrt(w)+K+mp.pi*mp.sqrt(a)*(a*a-3)/(8*a)*mp.sqrt(w)+(4-a**3)/(6*a)*w
            out['singular_checks'].append({'u':str(u),'w':str(w),'scaled_error':str((logh-approx)/w**mp.mpf('1.5'))})
    c_sym,g_sym,co=first_saddle(3);cofun=s.lambdify((c_sym,*g_sym),co,'mpmath')
    for u in [mp.mpc(1,'.08'),mp.mpc('.25','.01'),mp.mpc(4,'.1')]:
        v=mp.log(u);r,c,D=params(v);a=mp.exp(-v/2)
        gg=[mp.pi*mp.sqrt(a)*(a*a-3)/(8*a)*mp.sqrt(r),(4-a**3)/(6*a)*r,mp.pi*mp.sqrt(a)*(9*a**4+10*a*a-15)/(384*a*a)*r**mp.mpf('1.5')]
        aa=cofun(c,*gg)
        for n in [x for x in [100,200,400] if x<=args.n]:
            val=mp.polyval(list(reversed(A[n])),u);delta=mp.mpf(n)**(-mp.mpf(1)/3)
            lead=mp.factorial(n)*D*r**(-n)*mp.exp(3*c/delta)*n**(-mp.mpf(5)/6)
            err=(val/lead-sum(aa[j]*delta**j for j in range(4)))/delta**4
            out['complex_coefficient_checks'].append({'u':str(u),'n':n,'scaled_error':str(err)})
    out['elapsed_seconds']=time.monotonic()-start
    Path(__file__).with_name('validation.json').write_text(json.dumps(out,indent=2)+'\n')
    Path(__file__).with_name('exact_rows.json').write_text(json.dumps(A)+'\n')
    print('PASS independent joint word counts through',args.brute,'; exact rows through',args.n,'; elapsed',out['elapsed_seconds'])
    for r in out['refined_asymptotics'][-3:]:print(r)
if __name__=='__main__':main()

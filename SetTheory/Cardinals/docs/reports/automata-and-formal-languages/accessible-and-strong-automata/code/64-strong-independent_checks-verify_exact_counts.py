"""Independent exact-integer verification; never imports the coefficient generator.
A and labeled strong S use independent triangular integer recurrences.
Stirling diagonal uses exact surjection inclusion-exclusion.
"""
import argparse, json, math, time
from pathlib import Path
import mpmath as mp

def counts(k,N):
    A=[0]*(N+1); S=[0]*(N+1); facts=[math.factorial(n) for n in range(N+1)]
    for n in range(1,N+1):
        nk=n**k
        power=nk
        choose=n
        accum=0
        for h in range(n-1,0,-1):
            accum+=choose*power*A[h]
            power*=nk
            choose=choose*h//(n-h+1)
        A[n]=n**(k*n)-accum
        assert A[n]>0 and A[n]%facts[n]==0
        strong=n*A[n]
        choose=1
        for j in range(1,n):
            choose=choose*(n-j+1)//j
            strong+=(n-j)*choose*S[n-j]*A[j]
        assert strong%n==0
        S[n]=strong//n
        assert S[n]>0
        if n%100==0: print(f'k={k}, exact recurrences through n={n}',flush=True)
    return A,S,facts

def stirling_diagonal(k,n):
    # n! S(kn,n) counts surjective maps [kn] -> [n]
    total=sum((-1)**(n-j)*math.comb(n,j)*j**(k*n) for j in range(n+1))
    assert total%math.factorial(n)==0
    return total//math.factorial(n)

def run(k,N,coef):
    mp.mp.dps=100
    A,S,facts=counts(k,N)
    result={'k':k,'n_max':N,'first_A':A[1:7],'first_labeled_strong':S[1:7],'samples':[]}
    if coef:
        v=mp.mpf(coef['v']); c=k*v-k+1; rho=1-v
        d=k-1
        p1=-k*rho*v/(2*c)-(c*v if k==2 else 0)
        b1=-k*rho*v/(2*c)-(c*v*v if k==2 else 0)
        result['closed_first_order_differences']={
          'p1':mp.nstr(mp.mpf(coef['p'][1])-p1,60),
          'b1':mp.nstr(mp.mpf(coef['b'][1])-b1,60)}
    for n in [100,150,200,300,400,500,600,800,1000]:
        if n>N:continue
        T=stirling_diagonal(k,n)
        pr=mp.mpf(A[n])/(facts[n]*T)
        br=mp.mpf(S[n])/(facts[n]*T)
        entry={'n':n,'P_over_T':mp.nstr(pr,90),'B_over_T':mp.nstr(br,90)}
        if coef:
            for label,ratio in [('p',pr),('b',br)]:
                C=[mp.mpf(c) for c in coef[label]]
                residual=ratio
                scaled=[]
                for j,c in enumerate(C):
                    residual-=c/mp.mpf(n)**j
                    scaled.append(mp.nstr(residual*mp.mpf(n)**(j+1),40))
                entry[label+'_scaled_remainders']=scaled
        result['samples'].append(entry)
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--k',type=int,required=True);p.add_argument('--N',type=int,default=600);p.add_argument('--coefficients');p.add_argument('--output',required=True);args=p.parse_args()
    t=time.time();co=json.loads(Path(args.coefficients).read_text()) if args.coefficients else None
    result=run(args.k,args.N,co);result['seconds']=time.time()-t
    Path(args.output).write_text(json.dumps(result,indent=2)+'\n');print('wrote',args.output,'in',result['seconds'],'seconds')

"""Independent stable-tiling asymptotic coefficients; no guessed recurrence."""
import json, math, sys
from pathlib import Path
import sympy as S
k = S.symbols("k")

def parts(total, low=1):
    if total == 0:
        yield ()
    else:
        for d in range(low, total + 1):
            for tail in parts(total-d, d):
                yield (d,) + tail

def conv(a,b,K):
    c=[S.Integer(0)]*(K+1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            if i+j<=K:
                c[i+j] += x*y
    return [S.expand(x) for x in c]

def exp_series(logs,K):
    out=[S.Integer(1)]
    for n in range(1,K+1):
        out.append(S.expand(sum(j*logs[j]*out[n-j] for j in range(1,n+1))/n))
    return out

def power_sum(A,B,p):
    return S.expand((S.bernoulli(p+1,A+B)-S.bernoulli(p+1,A))/(p+1))

def stable(r, counts, c, j, K):
    weights=[S.Integer(1)] + [S.Integer(0)]*K
    for d,a in counts.items():
        factor=[S.binomial(a,h)*(d+1)**h for h in range(min(a,K)+1)]
        weights=conv(weights,factor,K)
    out=[S.Integer(0)]*(K+1)
    for h in range(K+1):
        e=S.expand(sum(S.ff(k,q)/S.factorial(q)*weights[h-q] for q in range(h+1)))
        pref=(-1)**h*S.rf(r-1,h)*e
        if pref==0: continue
        logs=[S.Integer(0)]+[-power_sum(j+h,c-h,p)/p for p in range(1,K-h+1)]
        arr=exp_series(logs,K-h)
        for t,x in enumerate(arr):
            out[h+t]+=pref*x
    return [S.expand(x) for x in out]

def poisson_sum(poly):
    P=S.Poly(S.expand(poly),k)
    total=0
    for (power,),coeff in P.terms():
        # e sum_{k>=0} (-1)^k k^power/k! = Touchard_power(-1).
        total+=coeff*sum((-1)**j*S.functions.combinatorial.numbers.stirling(power,j,kind=2)
                         for j in range(power+1))
    return S.factor(total)

def compute(r,s,K):
    answer=[S.Integer(0)]*(K+1)
    for D in range(K+1):
        for profile in parts(D):
            counts={d:profile.count(d) for d in set(profile)}
            L=len(profile); c=k+L; j=c+D
            M=K-D
            sr=stable(r,counts,c,j,M)
            ss=sr if r==s else stable(s,counts,c,j,M)
            logs=[S.Integer(0)]+[power_sum(0,2*c+D,p)/p for p in range(1,M+1)]
            ratio=exp_series(logs,M)
            block=conv(conv(sr,ss,M),ratio,M)
            factor=S.Rational((-1)**(L+D), math.prod(math.factorial(a) for a in counts.values()))
            for t,x in enumerate(block):
                answer[D+t]+=factor*poisson_sum(x)
    return [S.factor(x) for x in answer]

if __name__=="__main__":
    r,s,K=map(int,sys.argv[1:4])
    vals=compute(r,s,K)
    data={"r":r,"s":s,"order":K,"coefficients":[str(x) for x in vals],
          "normalization":"a_rs(n)/n! ~ exp(-1) sum_j coefficients[j]/n^j",
          "method":"paired tilings, stable long-chain coefficient, exact Poisson polynomial moments"}
    p=Path(__file__).with_name(f"coefficients_{r}_{s}_{K}.json")
    p.write_text(json.dumps(data,indent=2)+"\n")
    print(json.dumps(data,indent=2))

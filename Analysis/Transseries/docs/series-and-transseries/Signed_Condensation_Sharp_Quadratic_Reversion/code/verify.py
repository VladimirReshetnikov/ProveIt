#!/usr/bin/env python3
"""Exact checks and floating diagnostics for quadratic-feedback reversion.

No network access is used. Exact arithmetic uses Python integers/Fraction.
The asymptotic diagnostic table uses mpmath; it is not an interval proof.
Run: python code/verify.py --degree 320
(ed. 2026-09-29: the default degree is now 320, that of the recorded run;
outputs go to rerun/ beside code/ unless --output-dir is given, and writing
into the recorded data/ needs --overwrite-recorded. All files and standard
output are written with LF.)
"""
from __future__ import annotations
import argparse, csv, json, math, sys, time
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
import mpmath as mp

@dataclass(frozen=True)
class Model:
    name: str
    a: int = 1
    b: int = 0
    d: int = 0
    lambda1: int | None = None
    weight2: int = 1
    def slope(self, j: int) -> int:
        if j == 1 and self.lambda1 is not None:
            return self.lambda1
        return self.a*j*j + self.b*j + self.d
    def weight(self, j: int) -> int:
        return self.weight2 if j == 2 else 1
    @property
    def beta(self) -> int:
        return self.slope(1) + self.weight2


def inverse_egf(model: Model, N: int) -> list[int]:
    """Return V[n]=n! [u^n]Q(u), via the defining inverse kernel.

    P[j][n] is n![u^n]Q(u)^j. Its recurrence follows from
    (Q^j)'=j Q' Q^(j-1). The kernel is imposed degree by degree.
    """
    if N < 1: raise ValueError('N must be positive')
    C = [[math.comb(n,k) for k in range(n+1)] for n in range(N+1)]
    powers = [[pow(model.slope(j),h) for h in range(N+1)] for j in range(N+1)]
    P = [[0]*(N+1) for _ in range(N+1)]
    V=P[1]; V[1]=1
    for n in range(2,N+1):
        for j in range(2,n+1):
            P[j][n]=j*sum(C[n-1][k-1]*V[k]*P[j-1][n-k]
                          for k in range(1,n-j+2))
        value=sum(C[n][k]*V[k]*powers[1][n-k] for k in range(1,n))
        for j in range(2,n+1):
            if model.weight(j):
                value += model.weight(j)*sum(C[n][k]*P[j][k]*powers[j][n-k]
                                             for k in range(j,n+1))
        V[n]=-value
    return V


def multiplicities(total: int, lo: int=1):
    """Yield partitions of 'total' as nondecreasing positive excesses."""
    if total==0:
        yield ()
    else:
        for x in range(lo,total+1):
            for tail in multiplicities(total-x,x):
                yield (x,)+tail


def inverse_partition(model: Model,n: int, cutoff: int|None=None) -> Fraction:
    """Independent finite multivariate Lagrange formula.

    cutoff=None: full coefficient. cutoff=M: exactly one primitive j>M.
    """
    ans=Fraction((-model.slope(1))**(n-1),math.factorial(n-1)) if cutoff is None else Fraction(0)
    for L in range(1,n):
        h=n-1-L
        for part in multiplicities(L):
            js=[x+1 for x in part]
            if cutoff is not None and sum(j>cutoff for j in js)!=1: continue
            counts={j:js.count(j) for j in set(js)}
            k=len(js)
            lam=sum((model.slope(j)-j*model.slope(1))*m for j,m in counts.items())-model.slope(1)
            num=(-1)**k*math.factorial(L+k)*lam**h
            den=math.factorial(L+1)*math.factorial(h)
            for j,m in counts.items():
                num*=model.weight(j)**m; den*=math.factorial(m)
            ans+=Fraction(num,den)
    return ans


def mul(A:list[Fraction],B:list[Fraction],N:int)->list[Fraction]:
    out=[Fraction(0)]*(N+1)
    for i,a in enumerate(A[:N+1]):
        if a:
            for j,b in enumerate(B[:N+1-i]):
                if b:out[i+j]+=a*b
    return out


def analytic_core_response(model:Model,M:int,N:int)->list[Fraction]:
    """One-tail response -Q_M^j exp(lambda_j u)/F_{M,q}, summed over j>M.
    Independently compute Q_M by truncated polynomial operations.
    """
    zero=Fraction(0); one=Fraction(1)
    def exp_linear(lam:int):return [Fraction(lam**h,math.factorial(h)) for h in range(N+1)]
    exps=[exp_linear(model.slope(j)) for j in range(N+1)]
    Q=[zero]*(N+1); Q[1]=one
    def qpowers(Q):
        p=[[one]+[zero]*N,Q[:]]
        for j in range(2,N+1):p.append(mul(p[-1],Q,N))
        return p
    for n in range(2,N+1):
        ps=qpowers(Q)
        Q[n]=-sum(model.weight(j)*mul(ps[j],exps[j],n)[n] for j in range(1,min(M,n)+1))
    ps=qpowers(Q)
    D=[zero]*(N+1)
    for j in range(1,M+1):
        term=mul(ps[j-1],exps[j],N)
        for h in range(N+1):D[h]+=j*model.weight(j)*term[h]
    A=[zero]*(N+1); A[0]=one
    for n in range(1,N+1):A[n]=-sum(D[k]*A[n-k] for k in range(1,n+1))
    out=[zero]*(N+1)
    for j in range(M+1,N+1):
        term=mul(A,mul(ps[j],exps[j],N),N)
        for h in range(N+1):out[h]-=model.weight(j)*term[h]
    return out


def saddle(n:int,a:int):
    # Bisection is robust even at low n.
    lo=mp.mpf(0); hi=max(mp.mpf(1),mp.log(a*n+1))
    for _ in range(4*mp.mp.dps):
        r=(lo+hi)/2
        if r*(r+1)*mp.exp(2*r)<a*n:lo=r
        else:hi=r
    r=(lo+hi)/2; k=mp.mpf(n)*r/(r+1)
    logS=k*(1+2*r)-mp.log(1+4*r+2*r*r)/2
    return r,logS


def main():
    try:  # ed. 2026-09-29: LF also in redirected stdout on Windows
        sys.stdout.reconfigure(newline='\n')
    except AttributeError:
        pass
    root=Path(__file__).resolve().parents[1]
    parser=argparse.ArgumentParser();parser.add_argument('--degree',type=int,default=320)
    parser.add_argument('--output-dir',type=Path,default=root/'rerun')
    parser.add_argument('--overwrite-recorded',action='store_true',
                        help='allow writing into the recorded data/ directory')
    args=parser.parse_args(); N=args.degree
    if not 20<=N<=1200:raise ValueError('degree must lie in [20,1200]')
    out=args.output_dir
    if out.resolve()==(root/'data').resolve() and not args.overwrite_recorded:
        parser.error('refusing to overwrite the recorded data/; pass --overwrite-recorded or choose another --output-dir')
    out.mkdir(parents=True,exist_ok=True)
    models=[Model('pure_a1'),Model('pure_a2',a=2),Model('lambda1_zero',lambda1=0),
            Model('linear_tail',b=1),Model('weight2_two',weight2=2)]
    checks=0; start=time.perf_counter(); all_data={}
    mp.mp.dps=90
    for idx,model in enumerate(models):
        degree=N if idx==0 else min(N,160)
        V=inverse_egf(model,degree); all_data[model.name]=(model,V)
        for n in range(1,15):
            assert Fraction(V[n],math.factorial(n))==inverse_partition(model,n)
            checks+=1
        for M in (1,2,3):
            response=analytic_core_response(model,M,12)
            for n in range(1,13):
                assert response[n]==inverse_partition(model,n,M)
                checks+=1
        assert Fraction(V[2],2)==-model.beta;checks+=1
        with (out/f'{model.name}_exact_egf.csv').open('w',newline='') as f:
            wr=csv.writer(f,lineterminator='\n');wr.writerow(['n','n_factorial_times_v_n']);wr.writerows(enumerate(V))
        print(f'{model.name}: exact coefficients through {degree}; checks passed',flush=True)
    rows=[]
    for name,(model,V) in all_data.items():
        for n in (20,50,100,160,200,240,300,320,400,500,600):
            if n>=len(V):continue
            r,logS=saddle(n,model.a)
            c=mp.mpf(model.b-model.beta)/model.a
            ratio=-mp.mpf(V[n])/mp.factorial(n)*mp.exp(-logS-c*r)
            rows.append([name,n,mp.nstr(r,16),mp.nstr(ratio,16)])
    with (out/'asymptotic_diagnostics.csv').open('w',newline='') as f:
        wr=csv.writer(f,lineterminator='\n');wr.writerow(['model','n','r_n','v_n_over_predicted_negative_equivalent']);wr.writerows(rows)
    with (out/'table.tex').open('w',newline='\n') as f:
        for name,n,r,ratio in rows:
            if name=='pure_a1' and n in (20,50,100,160,200,240,300,320,400,500,600):
                f.write(f'{n} & {float(r):.6f} & {float(ratio):.9f} \\\\\n')
    status={'exact_assertions':checks,'max_degree':N,'models':len(models),
            'diagnostics_precision_decimal_digits':mp.mp.dps,
            'elapsed_seconds':round(time.perf_counter()-start,3),
            'status':'All exact checks passed. Asymptotic tables are floating diagnostics, not proof or interval certificates.'}
    (out/'verification.json').write_text(json.dumps(status,indent=2)+'\n',newline='\n')
    print(json.dumps(status,indent=2))
    for row in rows:print(', '.join(map(str,row)))

if __name__=='__main__':main()

#!/usr/bin/env python3
"""Independent arbitrary-precision diagnostic for raw harmonic-power Laurent data.

Continuation uses the finite original Dirichlet head and the Euler--Maclaurin
expansion of its digamma tail. No multiple-polylogarithm kernel or predicted
Laurent coefficients are used when evaluating the continued series. Laurent
coefficients are extracted by discrete Cauchy averages. This is a numerical
check, not a substitute for the all-index normal-convergence proof.
"""
import argparse, json, math, time
from pathlib import Path
import mpmath as mp


def convolution(a,b,K):
    c=[mp.mpf('0')]*(K+1)
    for j,x in enumerate(a):
        if not x:continue
        for k,y in enumerate(b[:K+1-j]):
            if y:c[j+k]+=x*y
    return c

class ContinuedPower:
    def __init__(self,p,a,N=100,K=26,J=16):
        self.p,self.a,self.N,self.K,self.J=p,mp.mpf(a),N,K,J
        self.X=self.a+N
        self.logX=mp.log(self.X)
        self.Q=mp.euler+self.logX
        self.head=[]
        H=mp.mpf('0')
        for n in range(N):
            if n:H+=mp.mpf(1)/n
            self.head.append((H**p,mp.log(n+self.a)))
        U=[mp.mpf('0')]+[-mp.bernpoly(k,self.a)/k for k in range(1,K+1)]
        powers=[[mp.mpf(1)]+[mp.mpf(0)]*K]
        for j in range(p):powers.append(convolution(powers[-1],U,K))
        self.terms=[]
        for k in range(K+1):
            coeffs=[mp.mpf(math.comb(p,r))*powers[p-r][k] for r in range(p+1)]
            if any(coeffs):self.terms.append((k,coeffs))
        self.bernoulli=[None]+[mp.bernoulli(2*j)/mp.factorial(2*j) for j in range(1,J+1)]
        self.binoms=[[mp.mpf(math.comb(r,h))*mp.factorial(h)*(-1)**h*self.Q**(r-h) for h in range(r+1)] for r in range(p+1)]

    def moments(self,w,k):
        p,X,Q=self.p,self.X,self.Q
        exp=mp.exp((1-w)*self.logX)
        out=[]
        for r in range(p+1):
            v=sum(mp.mpf(math.comb(r,h))*mp.factorial(h)*Q**(r-h)/(w-1)**(h+1) for h in range(r+1))
            out.append(exp*(v+Q**r/(2*X)))
        maxj=min(self.J,max(2,(self.K-k)//2+3))
        poch=[mp.mpc(1)]+[mp.mpc(0)]*p
        n=0
        for j in range(1,maxj+1):
            while n<2*j-1:
                for h in range(p,0,-1):poch[h]=poch[h]*(w+n)+poch[h-1]
                poch[0]*=w+n
                n+=1
            weight=self.bernoulli[j]*exp/X**(2*j)
            for r in range(p+1):
                out[r]+=weight*sum(self.binoms[r][h]*poch[h] for h in range(r+1))
        return out

    def __call__(self,s):
        result=sum(v*mp.exp(-s*L) for v,L in self.head)
        for k,coeffs in self.terms:
            moments=self.moments(s+k,k)
            result+=sum(c*v for c,v in zip(coeffs,moments) if c)
        return result


def predicted(p,m,a):
    a=mp.mpf(a);g=mp.euler;b=a-mp.mpf('0.5')
    Q={1:mp.mpf('0.5'),2:mp.mpf(-1),3:3+mp.zeta(2)/2,4:-12-2*mp.zeta(2)+3*mp.zeta(3)}[p]
    T={1:mp.mpf(0),2:-mp.mpf(1)/12,3:mp.mpf(1)/8,4:-mp.mpf(1)/4}[p]
    out={j:mp.mpf(0) for j in range(-p,1)}
    if m==0:
        for j in range(-p,1):out[j]=-b*mp.factorial(p)*g**(p+j)/mp.factorial(p+j)
        out[0]+=Q
    elif m==1:
        A=mp.mpf(1)/24-b*b/2
        for j in range(-p,1):
            out[j]=mp.factorial(p)*A*g**(p+j)/mp.factorial(p+j)
            if p-1+j>=0:out[j]+=mp.factorial(p)*b*b/2*g**(p-1+j)/mp.factorial(p-1+j)
        out[0]+=b*Q+T
    elif m==2 and a==mp.mpf('0.5'):
        out[0]={1:-mp.mpf(1)/24,2:mp.mpf(1)/36,3:-mp.mpf(1)/9-mp.zeta(2)/24,4:mp.mpf(13)/27+mp.zeta(2)/18-mp.zeta(3)/4}[p]
    else:raise ValueError((p,m,a))
    return out


def cauchy_case(p,m,a,N,K,J,samples,radius):
    fun=ContinuedPower(p,a,N=N,K=K,J=J)
    sums={j:mp.mpc(0) for j in range(-p,1)}
    for k in range(samples):
        epsilon=radius*mp.exp(2j*mp.pi*(mp.mpf(k)+mp.mpf('0.5'))/samples)
        value=fun(-m+epsilon)
        for j in sums:sums[j]+=value*epsilon**(-j)/samples
    want=predicted(p,m,a)
    rows=[]
    for j,v in sums.items():
        err=abs(v-want[j])
        rows.append({'laurent_power':j,'computed_real':mp.nstr(v.real,45),'computed_imag':mp.nstr(v.imag,5),'expected':mp.nstr(want[j],45),'absolute_error':mp.nstr(err,8)})
    return {'p':p,'spectral_center':-m,'a':str(a),'max_error':mp.nstr(max(abs(sums[j]-want[j]) for j in sums),8),'coefficients':rows}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--quick',action='store_true')
    args=ap.parse_args()
    mp.mp.dps=58
    N,K,J,samples=100,26,16,32
    radius=mp.mpf('0.035')
    cases=[(p,m,'0.5') for p in (2,3,4) for m in (0,1,2)]
    cases += [(p,m,'0.75') for p in (2,3,4) for m in (0,1)]
    if args.quick:cases=[(2,0,'0.5'),(3,1,'0.75'),(4,2,'0.5')]
    result={'method':'Original Dirichlet head plus independent digamma-tail Euler--Maclaurin continuation; discrete Cauchy extraction','working_dps':mp.mp.dps,'N':N,'K':K,'J':J,'cauchy_samples':samples,'cauchy_radius':str(radius),'cases':[]}
    start=time.time()
    for p,m,a in cases:
        row=cauchy_case(p,m,a,N,K,J,samples,radius)
        result['cases'].append(row)
        print(p,m,a,row['max_error'],flush=True)
    result['stability_replay']=[]
    if not args.quick:
        for p,m,a in [(2,0,'0.75'),(3,1,'0.75'),(4,2,'0.5')]:
            row=cauchy_case(p,m,a,120,28,18,40,mp.mpf('0.03'))
            result['stability_replay'].append(row)
            print('REPLAY',p,m,a,row['max_error'],flush=True)
        result['replay_settings']={'N':120,'K':28,'J':18,'cauchy_samples':40,'cauchy_radius':'0.03'}
    result['max_error']=mp.nstr(max(mp.mpf(r['max_error']) for r in result['cases']+result['stability_replay']),8)
    result['elapsed_seconds']=time.time()-start
    result['check_status']='PASS' if mp.mpf(result['max_error'])<mp.mpf('1e-30') else 'FAIL'
    out=Path(__file__).resolve().parents[1]/'results'/'harmonic_numerical_checks.json'
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(result,indent=2)+'\n')
    print('RESULT',result['check_status'],result['max_error'],result['elapsed_seconds'],flush=True)
    if result['check_status']!='PASS':raise SystemExit(1)

if __name__=='__main__':main()

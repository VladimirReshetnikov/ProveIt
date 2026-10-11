"""Independent local integral versus Gamma integral plus tail-spectrum formula."""
from pathlib import Path
import json
import mpmath as mp
import sympy as sp
from compute_appell import compute, h, A, v, z, p2, nice

mp.mp.dps=80
BASE=Path(__file__).parent

def conv(a,b,N):
    out=[mp.mpf('0')]*(N+1)
    for j,aa in enumerate(a):
        if not aa:continue
        for k,bb in enumerate(b[:N-j+1]):
            if bb:out[j+k]+=aa*bb
    return out

def Bcoeff(m):
    b=[mp.mpf(1),mp.mpf(0)]
    for j in range(2,m+1):b.append(mp.fsum(mp.zeta(r)*b[j-r] for r in range(2,j+1))/j)
    return b

def direct_integral(m,N=210):
    b=Bcoeff(m)
    # x*(psi(x)+gamma) = -1 + sum_{r>=2} (-1)^r*zeta(r)*x^r.
    f=[mp.mpf(-1),mp.mpf(0)]+[(-1)**r*mp.zeta(r) for r in range(2,N+1)]
    power=[mp.mpf(1)]+[mp.mpf(0)]*N
    coeff=[mp.mpf(0)]*(N+1)
    for k in range(m+1):
        c=mp.factorial(m)*b[m-k]/mp.factorial(k)
        for j in range(N-(m-k)+1):coeff[j+m-k]+=c*power[j]
        if k<m:power=conv(power,f,N)
    a=mp.mpf('0.5')
    low=mp.fsum(aa*(mp.log(a) if j==m-1 else a**(j-m+1)/(j-m+1)) for j,aa in enumerate(coeff))
    def fmp(x):
        yy=mp.digamma(x)+mp.euler
        return mp.factorial(m)*mp.fsum(b[m-k]*yy**k/mp.factorial(k) for k in range(m+1))
    return low+mp.quad(fmp,[a,mp.mpf('.75'),1])

def gamma_integral(m):
    def integrand(t):
        if not t:return mp.mpf(0)
        yy=mp.exp(-t)
        if yy==1:return mp.mpf(0)
        if yy<mp.mpf('1e-25'):
            K=mp.mpf('0.5')+mp.mpf(5)*yy/6+mp.mpf(9)*yy**2/8
        else:
            L=-mp.log1p(-yy)
            K=(L-yy)/((1-yy)**2*L**2)
        return -t**m*yy*K
    return mp.quad(integrand,[0,1,4,16,40,mp.inf])

def asymptotic_spectrum(m,N=96,M=42):
    data=compute(m)
    ll,gg=sp.symbols('ll gg')
    h_exp=ll+gg-v/2-sum(sp.bernoulli(2*k)*v**(2*k)/(2*k) for k in range(1,M//2+1))
    tail_exp={A[r-1]:v**(r-1)/sp.Integer(r-1)-v**r/2+sum(sp.bernoulli(2*k)*sp.rf(r,2*k-1)*v**(r+2*k-1)/sp.factorial(2*k) for k in range(1,M//2+1) if r+2*k-1<=M) for r in range(2,m)}
    # Truncated polynomial multiplication prevents huge discarded expressions.
    def as_poly(x):return {int(k[0]):c for k,c in sp.Poly(x,v).terms() if k[0]<=M}
    def mul(a,b):
        out={}
        for j,c in a.items():
            for k,d in b.items():
                if j+k<=M:out[j+k]=out.get(j+k,0)+c*d
        return {k:sp.expand(c) for k,c in out.items() if c}
    expansions={h[0]:as_poly(h_exp),**{a:as_poly(e) for a,e in tail_exp.items()}}
    total={}
    variables=[h[0],*A[1:m-1]]
    for powers,c in sp.Poly(data['dt'],v,*variables).terms():
        q,*rest=powers
        term={q:c}
        for sym,count in zip(variables,rest):
            for _ in range(count):term=mul(term,expansions[sym])
        for k,d in term.items():total[k]=total.get(k,0)+d
    constants={p2:mp.pi**2,gg:mp.euler,**{sym:mp.zeta(r) for r,sym in z.items()}}
    def to_mp(expr):return mp.mpf(str(sp.N(expr.subs({k:str(c) for k,c in constants.items()}),mp.mp.dps)))
    tail=mp.mpf(0)
    for q,coeff in total.items():
        for (r,),c in sp.Poly(sp.expand(coeff),ll).terms():
            # minus sum dt(n)*log(n)
            tail-=to_mp(c)*(-1)**(r+1)*mp.diff(lambda s:mp.zeta(s,N+1),q,r+1)
    args=[v,h[0],*A[1:m-1],p2,*[z[r] for r in range(3,m,2)]]
    fn=sp.lambdify(args,data['dt'],'mpmath')
    def delta(n):return fn(mp.mpf(1)/n,mp.digamma(n)+mp.euler,*[mp.zeta(r,n+1) for r in range(2,m)],mp.pi**2,*[mp.zeta(r) for r in range(3,m,2)])
    initial=-mp.fsum(delta(n)*mp.log(n) for n in range(1,N+1))
    return initial+tail

def main():
    out=[]
    for m in [6,7]:
        direct=direct_integral(m)
        cm=gamma_integral(m)
        ds=asymptotic_spectrum(m)
        jj=245*mp.zeta(2)*mp.zeta(3)+175*mp.zeta(5) if m==6 else mp.mpf(3731)*mp.zeta(3)**2/4+mp.mpf(918631)*mp.zeta(6)/240
        rebuilt=cm+jj+ds
        row={k:mp.nstr(val,75) for k,val in dict(direct=direct,gamma_integral=cm,J=jj,Dprime=ds,reconstructed=rebuilt,error=abs(direct-rebuilt)).items()}
        row.update(m=m,dps=mp.mp.dps,N=96,M=42,kind='non-interval numerical diagnostic')
        print(json.dumps(row),flush=True)
        out.append(row)
        assert abs(direct-rebuilt)<mp.mpf('1e-42')
    (BASE/'numeric_appell.json').write_text(json.dumps(out,indent=2))

if __name__=='__main__':main()

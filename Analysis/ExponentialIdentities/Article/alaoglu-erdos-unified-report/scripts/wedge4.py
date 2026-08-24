import mpmath as mp, random, math, time, json, sys
from collections import Counter
from fractions import Fraction
from sympy import primerange
mp.mp.dps = 300
random.seed(4242)

X = 10**5
PRIMES = [p for p in primerange(5, X)]
def qres(p,u):
    p2=p*p; return ((pow(u%p2,p-1,p2)-1)//p)%p
Q2={p:qres(p,2) for p in PRIMES}; Q3={p:qres(p,3) for p in PRIMES}
THETA = mp.log(3)/mp.log(2)

# EXACT heuristic mean: lambda = sum (1-1/p)^2 / p   (p | MA excluded; wedge uniform on F_p)
lam = Fraction(0)
for p in PRIMES:
    lam += Fraction((p-1)**2, p**3)
lam_f = float(lam)
print("EXACT heuristic lambda = sum_{5<=p<1e5} (1-1/p)^2/p =", lam_f)
print("naive sum 1/p                                       =", float(sum(Fraction(1,p) for p in PRIMES)))
var = float(sum(Fraction((p-1)**2,p**3)*(1-Fraction((p-1)**2,p**3)) for p in PRIMES))
print("variance of drop count per pair                     =", var)

def drops(M,A):
    out=[]
    for p in PRIMES:
        if M%p==0 or A%p==0: continue
        p2=p*p
        qM=((pow(M%p2,p-1,p2)-1)//p)%p
        qA=((pow(A%p2,p-1,p2)-1)//p)%p
        if (qM*Q3[p]-qA*Q2[p])%p==0: out.append(p)
    return out

def cand(n):
    M=random.randrange(2**n,2**(n+1)); A=int(mp.nint(mp.power(mp.mpf(M),THETA))); return M,A
def gen(n):
    return random.randrange(2**n,2**(n+1)), random.randrange(3**n,3**(n+1))

N=int(sys.argv[1]); n=100
res={}
for name,g in [("candidate",cand),("generic",gen)]:
    t0=time.time(); cnt=Counter(); tot=0; per=Counter(); alld=[]
    for i in range(N):
        M,A=g(n); d=drops(M,A); tot+=len(d); cnt[len(d)]+=1; alld+=d
        for p in d: per[p]+=1
    res[name]=dict(tot=tot,cnt=dict(cnt),per=dict(per))
    mean=tot/N; z=(mean-lam_f)/math.sqrt(var/N)
    print(f"\n{name}: N={N}  total drops={tot}  mean={mean:.5f}  lambda={lam_f:.5f}  z={z:+.3f}  ({time.time()-t0:.0f}s)")
    print("  counts:", dict(sorted(cnt.items())))
    # Poisson chi-square
    obs=[cnt.get(k,0) for k in range(0,6)]; obs.append(sum(v for k,v in cnt.items() if k>=6))
    expv=[N*math.exp(-lam_f)*lam_f**k/math.factorial(k) for k in range(0,6)]
    expv.append(N-sum(expv))
    chi=sum((o-e)**2/e for o,e in zip(obs,expv) if e>0)
    print("  Poisson(lambda) chi2 =", round(chi,3), "on ~6 df ; obs",obs," exp",[round(e,1) for e in expv])
    # band table with exact expectation
    print("  band          #p    observed   expected      ratio    z")
    for lo,hi in [(5,100),(100,1000),(1000,10000),(10000,100000)]:
        ps=[p for p in PRIMES if lo<=p<hi]
        o=sum(per.get(p,0) for p in ps)
        e=N*float(sum(Fraction((p-1)**2,p**3) for p in ps))
        v=N*float(sum(Fraction((p-1)**2,p**3)*(1-Fraction((p-1)**2,p**3)) for p in ps))
        print(f"  [{lo:>6},{hi:>6}) {len(ps):>5} {o:>10} {e:>11.2f} {o/e:>9.4f} {(o-e)/math.sqrt(v):>+7.2f}")
json.dump(res,open(r"C:/Users/vresh/AppData/Local/Temp/claude/C--ProveIt--claude-worktrees-synthesis-proposal-impl-8529fc/4b24ee6a-9384-4180-b599-bcc5abc3250f/scratchpad/res4.json","w"))

import mpmath as mp, random, math, time, json, sys
from collections import Counter
from sympy import primerange
mp.mp.dps = 300
random.seed(777)

X = 10**5
PRIMES = [p for p in primerange(5, X)]
P2 = {p: p*p for p in PRIMES}
def qres(p,u):
    p2=p*p; return ((pow(u%p2,p-1,p2)-1)//p)%p
Q2={p:qres(p,2) for p in PRIMES}; Q3={p:qres(p,3) for p in PRIMES}
THETA = mp.log(3)/mp.log(2)

def drops(M,A):
    out=[]
    for p in PRIMES:
        if M%p==0 or A%p==0: continue
        p2=P2[p]
        qM=((pow(M%p2,p-1,p2)-1)//p)%p
        qA=((pow(A%p2,p-1,p2)-1)//p)%p
        if (qM*Q3[p]-qA*Q2[p])%p==0: out.append(p)
    return out

def cand(n):
    M=random.randrange(2**n,2**(n+1)); A=int(mp.nint(mp.power(mp.mpf(M),THETA))); return M,A
def gen(n):
    return random.randrange(2**n,2**(n+1)), random.randrange(3**n,3**(n+1))

N=int(sys.argv[1]); n=100
out={}
for name,g in [("candidate",cand),("generic",gen)]:
    t0=time.time(); per=Counter(); cnt=Counter(); tot=0
    for i in range(N):
        M,A=g(n); d=drops(M,A)
        tot+=len(d); cnt[len(d)]+=1
        for p in d: per[p]+=1
    out[name]=dict(tot=tot,cnt=dict(cnt),per=dict(per),secs=round(time.time()-t0,1))
    print(f"{name}: N={N} tot={tot} mean={tot/N:.5f} time={out[name]['secs']}s")
    print("   count distribution:", dict(sorted(cnt.items())))

exp = float(sum(mp.mpf(1)/p for p in PRIMES))
print("expected mean (sum 1/p, 5<=p<1e5) =", round(exp,6))
for name in out:
    tot=out[name]['tot']; m=tot/N
    sd = math.sqrt(sum(1.0/p*(1-1.0/p) for p in PRIMES)/N)
    print(f"  {name}: mean={m:.5f}  expected={exp:.5f}  z=({m-exp:.5f})/{sd:.5f} = {(m-exp)/sd:+.3f}")

# per-prime aggregation in dyadic bands: observed vs expected N/p
print("\nband        #primes   observed   expected(N*sum 1/p)   ratio")
bands=[(5,100),(100,1000),(1000,10000),(10000,100000)]
for name in out:
    print(" --",name)
    for lo,hi in bands:
        ps=[p for p in PRIMES if lo<=p<hi]
        obs=sum(out[name]['per'].get(p,0) for p in ps)
        expb=N*sum(1.0/p for p in ps)
        print(f" [{lo:>6},{hi:>6})  {len(ps):>6}   {obs:>8}   {expb:>18.3f}   {obs/expb if expb else float('nan'):>6.3f}")
json.dump(out,open(r"C:/Users/vresh/AppData/Local/Temp/claude/C--ProveIt--claude-worktrees-synthesis-proposal-impl-8529fc/4b24ee6a-9384-4180-b599-bcc5abc3250f/scratchpad/res3.json","w"))

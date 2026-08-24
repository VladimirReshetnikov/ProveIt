import mpmath as mp, random, math, time, json
from sympy import primerange
mp.mp.dps = 300
random.seed(20260823)

X = 10**5
PRIMES = [p for p in primerange(5, X)]
P2 = {p: p*p for p in PRIMES}

def qres(p, u, p2=None):
    if p2 is None: p2 = p*p
    return ((pow(u % p2, p-1, p2) - 1) // p) % p

Q2 = {p: qres(p,2) for p in PRIMES}
Q3 = {p: qres(p,3) for p in PRIMES}

THETA = mp.log(3)/mp.log(2)

def drop_primes(M, A):
    """list of p in [5,1e5) with Delta_p(M,A)=0; and list of p | MA (undefined)."""
    drops = []; bad = []
    for p in PRIMES:
        if M % p == 0 or A % p == 0:
            bad.append(p); continue
        p2 = P2[p]
        qM = ((pow(M % p2, p-1, p2) - 1)//p) % p
        qA = ((pow(A % p2, p-1, p2) - 1)//p) % p
        if (qM*Q3[p] - qA*Q2[p]) % p == 0:
            drops.append(p)
    return drops, bad

def candidate_pair(n):
    M = random.randrange(2**n, 2**(n+1))
    A = int(mp.nint(mp.power(mp.mpf(M), THETA)))
    return M, A

def generic_pair(n):
    M = random.randrange(2**n, 2**(n+1))
    A = random.randrange(3**n, 3**n*3)
    return M, A

def arch_defect(M, A):
    return mp.log(2)*mp.log(A) - mp.log(3)*mp.log(M)

N_PAIRS = int(__import__('sys').argv[1]) if len(__import__('sys').argv)>1 else 60
n = 100

results = {}
for name, gen in [("candidate", candidate_pair), ("generic", generic_pair)]:
    t0=time.time(); tot=0; counts=[]; alldrops=[]
    maxdef = mp.mpf(0)
    for i in range(N_PAIRS):
        M,A = gen(n)
        d = arch_defect(M,A)
        rel = abs(d)/(mp.log(2)*mp.log(A))
        if rel>maxdef: maxdef=rel
        dr,bad = drop_primes(M,A)
        counts.append(len(dr)); alldrops += dr; tot += len(dr)
    results[name] = dict(counts=counts, total=tot, drops=alldrops,
                         maxrel=mp.nstr(maxdef,6), secs=round(time.time()-t0,1))
    print(f"{name}: {N_PAIRS} pairs, total rank-drop primes = {tot}, "
          f"mean/pair = {tot/N_PAIRS:.4f}, max rel arch defect = {mp.nstr(maxdef,6)}, "
          f"{results[name]['secs']}s")

# controls
ctot=0
for m in range(1, 41):
    dr,bad = drop_primes(2**m, 3**m)
    ctot += len(dr)
    if m<=3 or m==40:
        print(f"control m={m}: rank-drop primes = {len(dr)} of {len(PRIMES)-len(bad)} usable, bad(p|MA)={len(bad)}")
print("controls m=1..40: total rank-drop =", ctot, " (expected 40*9588 =", 40*(len(PRIMES)-2),")")

exp_per_pair = float(sum(mp.mpf(1)/p for p in PRIMES))
print("expected rank-drops per pair under 1/p heuristic:", round(exp_per_pair,6))
print("candidate observed mean:", results['candidate']['total']/N_PAIRS)
print("generic   observed mean:", results['generic']['total']/N_PAIRS)
json.dump({k:{kk:vv for kk,vv in v.items()} for k,v in results.items()},
          open(r"C:/Users/vresh/AppData/Local/Temp/claude/C--ProveIt--claude-worktrees-synthesis-proposal-impl-8529fc/4b24ee6a-9384-4180-b599-bcc5abc3250f/scratchpad/res.json","w"))

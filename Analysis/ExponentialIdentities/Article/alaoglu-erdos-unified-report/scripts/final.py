import json, math
from fractions import Fraction
from sympy import primerange, factorint
import mpmath as mp
mp.mp.dps=50
PR=[p for p in primerange(5,10**5)]

# ---------- exact threshold arithmetic for part (2) ----------
theta_all = float(sum(mp.log(p) for p in PR))          # sum_{5<=p<1e5} log p
lam  = float(sum(Fraction((p-1)**2,p**3) for p in PR)) # E[# drop primes]
Etau = float(sum(mp.mpf((p-1)**2)/mp.mpf(p**2)/ (p-1) * mp.log(p) for p in PR))  # E[sum tau_p log p]
print("theta*(1e5) = sum_{5<=p<1e5} log p          =", round(theta_all,3))
print("pi*(1e5)                                    =", len(PR))
print("E[#drop primes]  = sum (1-1/p)^2/p          =", round(lam,6))
print("E[sum tau_p log p] = sum (1-1/p)^2 log p/(p-1) =", round(Etau,6))
print("=> heuristic kappa = 2 - E[logE]/logG        =", round(2-Etau/theta_all,9))
print("   measured (200 candidate pairs)            = 1.99989083   (logE = 10.882)")
print("   control  (M,A)=(2^m,3^m): logE = logG*1   -> kappa = 1 exactly (tau_p>=1 at every p)")
print()
print("THRESHOLD: kappa = 2 - c requires sum_{p<Y} tau_p log p >= c*theta(Y).")
for c in [1.0,0.5,0.1,0.01,1e-3]:
    need_mass = c*theta_all
    need_cnt  = need_mass/math.log(10**5)   # cheapest way: use the largest primes
    print(f"  c={c:<6} needs log-mass {need_mass:12.2f} = {need_mass/Etau:9.1f}x heuristic;"
          f" at least {need_cnt:9.1f} drop primes (>= {need_cnt/len(PR)*100:6.3f}% of all)")
print("  observed mean drop count = 1.7027 primes  (0.01776% of 9590)")
print("  ratio needed/observed for c=1 :", round(theta_all/Etau,1))

# ---------- per-prime test of the 1/p law ----------
res=json.load(open(r"C:/Users/vresh/AppData/Local/Temp/claude/C--ProveIt--claude-worktrees-synthesis-proposal-impl-8529fc/4b24ee6a-9384-4180-b599-bcc5abc3250f/scratchpad/res4.json"))
print("\nper-prime drop frequency, N=1000 pairs each   (exact expectation (1-1/p)^2/p)")
print("   p    exp     cand  gen     z_cand  z_gen")
for p in [5,7,11,13,17,19,23,29,31,37]:
    e=float(Fraction((p-1)**2,p**3))*1000
    c=res['candidate']['per'].get(str(p),0); g=res['generic']['per'].get(str(p),0)
    sd=math.sqrt(e*(1-e/1000))
    print(f"{p:>4} {e:>8.2f} {c:>7} {g:>5}   {(c-e)/sd:>+7.2f} {(g-e)/sd:>+6.2f}")

# ---------- the ONLY genuine product formula: valuations ----------
print("\nvaluation product formula  D_inf = sum_p (v_p(A) log2 - v_p(M) log3) log p  (exact check)")
for (M,A) in [(2**7,3**7),(1000,123456),(2**5*3**2*7,5**3*11)]:
    lhs=mp.log(2)*mp.log(A)-mp.log(3)*mp.log(M)
    rhs=mp.mpf(0)
    for p,e in factorint(A).items(): rhs+=mp.log(2)*e*mp.log(p)
    for p,e in factorint(M).items(): rhs-=mp.log(3)*e*mp.log(p)
    print(f"  M={M} A={A}: lhs-rhs = {mp.nstr(lhs-rhs,5)}")

# ---------- rank-one characterisation check ----------
print("\ncheck: Delta_p(M,A)=0  <=>  (M,A) = (2^t u, 3^t w) mod p^2 with u^(p-1)=w^(p-1)=1")
import random; random.seed(5)
for p in [5,7,11,13,101]:
    p2=p*p
    def q(u): return ((pow(u%p2,p-1,p2)-1)//p)%p
    tei=[c for c in range(1,p2) if c%p and pow(c,p-1,p2)==1]
    S=set()
    for t in range(p):
        for u in tei:
            for w in tei:
                S.add(((pow(2,t,p2)*u)%p2,(pow(3,t,p2)*w)%p2))
    Z={(M,A) for M in range(1,p2) if M%p for A in range(1,p2) if A%p
       and (q(M)*q(3)-q(A)*q(2))%p==0}
    print(f"  p={p}: |zero set|={len(Z)}  |control-twist set|={len(S)}  equal={Z==S}  "
          f"(density {len(Z)}/{(p*(p-1))**2} = 1/{(p*(p-1))**2//len(Z)})")

#!/usr/bin/env python3
"""Exact and high-precision checks for Random Tree Stability.
The finite tests verify enumeration formulas, not the imported all-size
stable-polynomial classification. Python >=3.10; mpmath for numerical mode.
"""
from __future__ import annotations
import argparse, csv, heapq, itertools, json, math, time
from collections import Counter, deque
from fractions import Fraction as Q
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def coeff(k: int) -> Q:
    if k < 1: return Q(0)
    small = {1:Q(1),2:Q(1,2),3:Q(1,2),4:Q(2,3),5:Q(25,24),
             6:Q(13,8),7:Q(55,24),8:Q(21,8),9:Q(17,8)}
    return small.get(k,Q(9,8))

def cayley(n: int) -> int:
    return 1 if n <= 2 else n**(n-2)

def forest_count(n: int, roots: int) -> int:
    if not (1 <= roots <= n): raise ValueError('Require 1 <= roots <= n')
    return 1 if roots == n else roots*n**(n-roots-1)

def exact_histogram(n: int) -> Counter:
    """Counts (tree, marking) pairs by (number marked, hull vertices)."""
    if n < 1: raise ValueError('n must be positive')
    out=Counter({(0,0):cayley(n),(1,1):n*cayley(n)})
    for k in range(2,n+1):
        a=coeff(k)*math.factorial(k)
        assert a.denominator == 1
        for ell in range(k,n+1):
            out[k,ell]=(math.comb(n,k)*int(a)*math.perm(n-k,ell-k)
                *math.comb(ell-2,k-2)*forest_count(n,ell))
    return out

def prufer_tree(n: int, code: tuple[int,...]) -> list[set[int]]:
    adj=[set() for _ in range(n)]
    if n==1: return adj
    deg=[1]*n
    for a in code: deg[a]+=1
    leaves=[i for i in range(n) if deg[i]==1]; heapq.heapify(leaves)
    for a in code:
        b=heapq.heappop(leaves); adj[a].add(b); adj[b].add(a)
        deg[b]-=1;deg[a]-=1
        if deg[a]==1:heapq.heappush(leaves,a)
    a,b=leaves;adj[a].add(b);adj[b].add(a)
    return adj

def ade_shape(adj: dict[int,set[int]]) -> str | None:
    n=len(adj)
    if n==0:return None
    branches=[v for v in adj if len(adj[v])>=3]
    if not branches:return 'A'
    if any(len(adj[v])>=5 for v in adj):return None
    if any(len(adj[v])==4 for v in adj):
        return 'affine_D4' if n==5 and len(branches)==1 else None
    if len(branches)==1:
        v=branches[0]; arms=[]
        for w in adj[v]:
            last=v;cur=w;length=1
            while len(adj[cur])==2:
                nxt=next(z for z in adj[cur] if z!=last)
                last,cur=cur,nxt;length+=1
            arms.append(length)
        arms.sort(); a,b,c=arms
        if (a,b)==(1,1):return 'D'
        finite={(1,2,2):'E6',(1,2,3):'E7',(1,2,4):'E8',
                (2,2,2):'affine_E6',(1,3,3):'affine_E7',(1,2,5):'affine_E8'}
        return finite.get(tuple(arms))
    if len(branches)==2:
        a,b=branches
        # The two off-spine neighbors at each branch must be immediate leaves.
        def leaves_at(v):return sum(len(adj[w])==1 for w in adj[v])
        if leaves_at(a)==2 and leaves_at(b)==2:return 'affine_D'
    return None

def classify_marking(adj: list[set[int]], mask: int):
    marks={v for v in range(len(adj)) if mask>>v&1}
    k=len(marks)
    if k==0:return True,0,'empty'
    if k==1:return True,1,'A'
    alive=set(range(len(adj))); deg=[len(v) for v in adj]
    todo=deque(v for v in alive if v not in marks and deg[v]<=1)
    while todo:
        v=todo.popleft()
        if v not in alive:continue
        alive.remove(v)
        for w in adj[v]:
            if w in alive:
                deg[w]-=1
                if w not in marks and deg[w]<=1:todo.append(w)
    ell=len(alive)
    if any(deg[v]>=3 for v in alive-marks):return False,ell,None
    sk={v:set() for v in marks}
    for v in marks:
        for w in adj[v]&alive:
            last,cur=v,w
            while cur not in marks:
                nxt=next(z for z in adj[cur]&alive if z!=last)
                last,cur=cur,nxt
            sk[v].add(cur)
    kind=ade_shape(sk)
    return kind is not None,ell,kind

def numeric(n: int, p, dps: int=60):
    """O(n) evaluations; returns probability and five conditional moments."""
    import mpmath as mp
    if n < 1: raise ValueError('n must be positive')
    mp.mp.dps=dps;p=mp.mpf(p);q=1-p
    if not (0<p<1):raise ValueError('Numerical kernel requires 0 < p < 1')
    r=p/q;const=mp.mpf(9)/8
    # Work throughout after dividing the probability by q**n.
    total=1+n*r;km=n*r;k2=n*r;hm=n*r;h2=n*r;kh=n*r
    fall=mp.mpf(1)
    for ell in range(1,n+1):
        fall*=mp.mpf(n-ell+1)/n
        if ell<2:continue
        b=const*r*r*(1+r)**(ell-2)
        mean=2+(ell-2)*p
        b1=b*mean;b2=b*(mean*mean+(ell-2)*p*q)
        for k in range(2,min(9,ell)+1):
            dq=coeff(k)-Q(9,8);d=mp.mpf(dq.numerator)/dq.denominator
            corr=d*math.comb(ell-2,k-2)*r**k
            b+=corr;b1+=k*corr;b2+=k*k*corr
        fac=n*fall*ell
        w=fac*b;total+=w;km+=fac*b1;k2+=fac*b2
        hm+=ell*w;h2+=ell*ell*w;kh+=ell*fac*b1
    ek=km/total;eh=hm/total
    return {'probability':q**n*total,'scaled':total/n,
            'mean_K':ek,'mean_H':eh,'var_K':k2/total-ek**2,
            'var_H':h2/total-eh**2,'cov_KH':kh/total-ek*eh}

def psi(lam, dps:int=60):
    import mpmath as mp
    mp.mp.dps=dps;lam=mp.mpf(lam);c=mp.mpf(9)/8
    out=c*(lam**2+mp.sqrt(mp.pi/2)*lam**3*mp.exp(lam**2/2)
                     *(1+mp.erf(lam/mp.sqrt(2))))
    for k in range(2,10):
        d=coeff(k)-Q(9,8)
        alpha=mp.sqrt(mp.pi)*mp.power(2,1-mp.mpf(k)/2)/mp.gamma(mp.mpf(k-1)/2)
        out+=mp.mpf(d.numerator)/d.denominator*alpha*lam**k
    return out

def exact_tests(max_n:int=6):
    t=time.time();records=[];pairs=0;trees=0;checks=0
    for n in range(1,max_n+1):
        actual=Counter();seen=0
        codes=itertools.product(range(n),repeat=max(0,n-2))
        for code in codes:
            adj=prufer_tree(n,code);seen+=1
            for mask in range(1<<n):
                good,ell,_=classify_marking(adj,mask)
                if good:actual[mask.bit_count(),ell]+=1
                pairs+=1
        expected=exact_histogram(n)
        assert actual==expected,(n,actual-expected,expected-actual)
        assert seen==cayley(n);trees+=seen
        checks+=len(expected)
        records.append({'n':n,'trees':seen,'marked_pairs':seen*(1<<n),
                        'stable_by_k':[sum(v for (k,l),v in actual.items() if k==j)
                                       for j in range(n+1)],
                        'joint_bins_checked':len(expected)})
    import mpmath as mp
    mp.mp.dps=70;numeric_checks=0
    for n in range(2,19):
        h=exact_histogram(n)
        for pr in [Q(1,5),Q(1,2),Q(4,5)]:
            qr=1-pr
            sums=[sum(Q(count)*pr**k*qr**(n-k)*weight(k,l)
                      for (k,l),count in h.items())/cayley(n)
                  for weight in [lambda k,l:1,lambda k,l:k,lambda k,l:l,
                                 lambda k,l:k*k,lambda k,l:l*l,lambda k,l:k*l]]
            vv=[mp.mpf(x.numerator)/x.denominator for x in sums]
            exact=[vv[0],vv[1]/vv[0],vv[2]/vv[0],vv[3]/vv[0]-(vv[1]/vv[0])**2,
                   vv[4]/vv[0]-(vv[2]/vv[0])**2,
                   vv[5]/vv[0]-vv[1]*vv[2]/vv[0]**2]
            got=numeric(n,mp.mpf(pr.numerator)/pr.denominator,70)
            for key,val in zip(['probability','mean_K','mean_H','var_K','var_H','cov_KH'],exact):
                assert mp.almosteq(got[key],val,rel_eps=mp.mpf('1e-58'),abs_eps=mp.mpf('1e-58')),(n,pr,key)
                numeric_checks+=1
    results={'status':'PASS','trees_exhaustively_enumerated':trees,
             'marked_tree_pairs_exhaustively_enumerated':pairs,
             'exact_joint_bins_checked':checks,'high_precision_identity_checks':numeric_checks,
             'seconds':round(time.time()-t,3),'rows':records,
             'scope':'Enumeration checks use the repository ADE classification; no proof-assistant verification.'}
    (ROOT/'data'/'verification.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))

def tables():
    import mpmath as mp
    mp.mp.dps=60
    rows=[]
    for p in ['0.2','0.5','0.8']:
        for n in [100,500,2000]:
            a=numeric(n,p);pp=mp.mpf(p);q=1-pp
            approx=mp.mpf(9)/8*mp.sqrt(2*mp.pi)*pp**3*n**mp.mpf('2.5')*mp.exp(-pp*n)
            row={'n':n,'p':p,'probability':mp.nstr(a['probability'],16),
                 'asymptotic_ratio':mp.nstr(a['probability']/approx,14),
                 'mean_K':mp.nstr(a['mean_K'],14),'mean_K_prediction':mp.nstr(n*pp**2+3*q,14),
                 'mean_H':mp.nstr(a['mean_H'],14),'mean_H_prediction':mp.nstr(n*pp+q/pp,14)}
            rows.append(row)
    with (ROOT/'data'/'fixed_density.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
    critical=[]
    for lam in ['0.5','1','2','3']:
        for n in [100,1000,10000]:
            p=mp.mpf(lam)/mp.sqrt(n);v=numeric(n,p)
            critical.append({'n':n,'lambda':lam,'scaled_probability':mp.nstr(v['scaled'],16),
                 'Psi':mp.nstr(psi(lam),16),'ratio':mp.nstr(v['scaled']/psi(lam),14),
                 'conditional_mean_K':mp.nstr(v['mean_K'],14)})
    with (ROOT/'data'/'critical_window.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=critical[0]);w.writeheader();w.writerows(critical)
    print(json.dumps({'fixed_density':rows,'critical_window':critical},indent=2))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--max-n',type=int,default=6)
    ap.add_argument('--tables',action='store_true');args=ap.parse_args()
    if args.max_n < 1: ap.error('--max-n must be positive')
    (ROOT/'data').mkdir(exist_ok=True)
    exact_tests(args.max_n)
    if args.tables: tables()

#!/usr/bin/env python3
"""Independent A279558 checks: direct avoidance, transformed DP, scalar equation.
No non-standard dependency is needed for these checks.
"""
if not __debug__:
 raise RuntimeError("Auxiliary producer scripts require ordinary Python; run the active-guard companion with python3 checks/verify.py")
import collections, itertools, json, math, pathlib, time
P=pathlib.Path.cwd()

def dp(N):
    states={(0,0,0):1} # a=n-max, b=max-premax, type S=0/T=1
    totals=[]; hs=[]; levels=[]
    for n in range(N+1):
        h=[0]*(n+1)
        for (a,b,t),count in states.items(): h[a]+=count
        totals.append(sum(h)); hs.append(h)
        if n<=9: levels.append(states.copy())
        if n==N: break
        nxt=collections.defaultdict(int)
        rows=collections.defaultdict(dict)
        for (a,b,t),count in states.items():
            nxt[a+1,b,0]+=count
            rows[a].setdefault(b,[0,0])[t]+=count
        for a,row in rows.items():
            count=sum(sum(v) for v in row.values())
            for b in range(1,a+1): nxt[a+1-b,b,0]+=count
            ss=tt=0
            for b in range(max(row),0,-1):
                s,t=row.get(b,(0,0))
                tt+=t
                if ss+tt: nxt[a+1,b,1]+=ss+tt
                ss+=s
        states=dict(nxt)
    return totals,hs,levels

def brute_levels(N):
    """Tests exactly the forbidden relation on all triples ending at new entry."""
    seqs=[()]; totals=[]; levels=[]
    for n in range(N+1):
        counts=collections.defaultdict(int)
        for e in seqs:
            h=max(e,default=0); below={v for v in e if v<h}
            k=max(below,default=0)
            t=int(bool(e) and e[-1]!=h)
            counts[n-h,h-k,t]+=1
        totals.append(len(seqs)); levels.append(dict(counts))
        if n==N: break
        seqs=[e+(v,) for e in seqs for v in range(n+1)
              if not any(e[i]!=e[j] and e[j]>v and e[i]>=v
                         for i in range(n) for j in range(i+1,n))]
    return totals,levels

def polymul(A,B,N):
    C=collections.defaultdict(int)
    for (n,a),v in A.items():
        for (m,b),w in B.items():
            if n+m<=N: C[n+m,a+b]+=v*w
    return {k:v for k,v in C.items() if v}

def polyadd(*terms):
    C=collections.defaultdict(int)
    for s,A in terms:
        for k,v in A.items(): C[k]+=s*v
    return {k:v for k,v in C.items() if v}

def scalar_check(hs,N):
    H={(n,a):v for n,h in enumerate(hs[:N+1]) for a,v in enumerate(h) if v}
    HP=collections.defaultdict(int)
    for n,h in enumerate(hs[:N+1]):
        for a,v in enumerate(h):
            if not v: continue
            HP[n,0]+=v
            for m in range(1,N-n+1):
                q=sum(math.comb(a,j)*math.comb(m+j-1,m-j) for j in range(1,min(a,m)+1))
                HP[n+m,m]+=v*q
    # phi=1+zx/(1-zx)^2; d=(x-phi)/(zx); c=1-(1-zx)d.
    # Clear denominators: zx*A*H(phi) - [zx*A-(1-zx)B]H - B=0.
    A={(0,0):1,(1,1):-2,(2,2):1}; zx={(1,1):1}
    B=polyadd((1,polymul(A,{(0,1):1,(0,0):-1},N)),(-1,zx))
    zxA=polymul(zx,A,N)
    coeff=polyadd((1,zxA),(-1,polymul({(0,0):1,(1,1):-1},B,N)))
    residual=polyadd((1,polymul(zxA,HP,N)),(-1,polymul(coeff,H,N)),(-1,B))
    assert not residual, sorted(residual.items())[:10]
    return True

if __name__=='__main__':
    start=time.time(); totals,hs,levels=dp(150)
    brute,b_levels=brute_levels(9)
    assert totals[:10]==brute
    assert levels==b_levels, 'Failure of refined (a,b,type) statistics!'
    oeis=[1,1,2,5,15,52,200,830,3654,16869,80963,401300,2043610,10649335,56604706,306101789,1680515427,9350151066,52644525981,299573440044,1721096279910,9973780332100,58253436956769,342680286785978,2029076119114543,12086940652059449]
    assert totals[:len(oeis)]==oeis
    assert scalar_check(hs,40)
    (P/'a279558_n0_150.txt').write_text('\n'.join(f'{n} {v}' for n,v in enumerate(totals))+'\n')
    result={'direct_avoidance_n_max':9,'direct_avoidance_totals':brute,
            'refined_state_distributions_match':True,'oeis_prefix_terms_matched':len(oeis),
            'dp_n_max':150,'scalar_equation_full_bivariate_coefficients_through_z':40,
            'a150':totals[150]}
    (P/'verification_model.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

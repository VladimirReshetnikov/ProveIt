"""Exact-integer operator construction reduced modulo a prime.

Small finite tests of Anthropic eth/paper.pdf, Appendix B (47)--(55).
Modular ranks are lower bounds for characteristic-zero ranks. This is not
an implementation of the SAT algorithm and gives no asymptotic proof.
"""
from functools import lru_cache
from collections import Counter, defaultdict
from math import comb, factorial
import argparse, json, time
from pathlib import Path
import numpy as np

P = 1000003

@lru_cache(None)
def parts(n, cap=None):
    if n == 0:
        return ((),)
    if n < 0:
        return ()
    cap = n if cap is None else min(cap, n)
    return tuple((j,) + tail for j in range(cap, 0, -1)
                 for tail in parts(n-j, j))

def addpart(p, j):
    return tuple(sorted(p+(j,), reverse=True))

@lru_cache(None)
def action(mu, r, inp):
    """Map partition -> coefficient for t_mu[r](t_inp), using (O2)."""
    eout = sum(inp)+r
    if eout < 0:
        return ()
    if not mu:
        return ((inp, 1),) if r == 0 else ()
    n, rest = mu[0], mu[1:]
    result = defaultdict(int)
    for l in range(n, eout+1):
        c = comb(l-1, n-1) % P
        for out, a in action(rest, r-l, inp):
            result[addpart(out,l)] += c*a
    for k, mult in Counter(inp).items():
        c = ((-1)**(n-1) * comb(k+n-1,n-1) * k * mult) % P
        reduced = list(inp); reduced.remove(k)
        for out, a in action(rest, r+k, tuple(reduced)):
            result[out] += c*a
    return tuple((out,a%P) for out,a in result.items() if a%P)

@lru_cache(None)
def dualpoly(mu):
    out = {():1}
    for n in mu:
        nxt=defaultdict(int)
        for p,c in out.items():
            for j in range(1,n+1):
                nxt[addpart(p,j)] += c*((-1)**(n-1))*comb(n,j)
        out={p:c%P for p,c in nxt.items() if c%P}
    return tuple(out.items())

def bscale(mu):
    h=sum(mu)
    z=1
    for k,m in Counter(mu).items(): z*=k**m*factorial(m)
    return (factorial(h)//z)%P

def rankmod(a):
    a=np.array(a,dtype=np.int64,copy=True)
    row=0
    for col in range(a.shape[1]):
        p=next((r for r in range(row,a.shape[0]) if a[r,col]),None)
        if p is None: continue
        a[[row,p]]=a[[p,row]]
        a[row]=(a[row]*pow(int(a[row,col]),-1,P))%P
        if row+1<a.shape[0]:
            a[row+1:]=(a[row+1:]-a[row+1:,col,None]*a[row,None,:])%P
        row+=1
        if row==a.shape[0]: break
    return row

def piece(h,s):
    basis=parts(h); d=len(basis); idx={mu:i for i,mu in enumerate(basis)}
    result=np.zeros((d*d,d*d),dtype=np.int64)
    for i in range(2*h+1):
        E=s+i
        if E<0: continue
        inter=parts(E); eidx={mu:j for j,mu in enumerate(inter)}
        left=np.zeros((d*d,len(inter)),dtype=np.int64)
        right=np.zeros((len(inter),d*d),dtype=np.int64)
        for x,mu in enumerate(basis):
            for a,c in dualpoly(mu):
                scale=(c*comb(sum(a)+h,i))%P
                if not scale: continue
                for y,nu in enumerate(basis):
                    for sigma,v in action(a,E-h,nu):
                        j=eidx[sigma]
                        left[x*d+y,j]=(left[x*d+y,j]+scale*v)%P
        for v,mu in enumerate(basis):
            scale=bscale(mu)
            for j,sigma in enumerate(inter):
                for out,c in action(mu,h-E,sigma):
                    u=idx[out]
                    right[j,u*d+v]=scale*c%P
        result=(result+((-1)**i)*(left@right))%P
    return result

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--max-h',type=int,default=6)
    parser.add_argument('--all-s',action='store_true')
    parser.add_argument('--out',default=str(Path(__file__).resolve().parents[1] / 'replay_results' / 'rank_probe.json'))
    args=parser.parse_args(); results=[]
    if not 1 <= args.max_h <= 8:
        raise ValueError('This finite probe was validated only for 1 <= max-h <= 8')
    output_path=Path(args.out)
    output_path.parent.mkdir(parents=True,exist_ok=True)
    for h in range(1,args.max_h+1):
        start=time.time();d=len(parts(h))
        ss=range(-2*h,2*h+1) if args.all_s else [0]
        total=np.zeros((d*d,d*d),dtype=np.int64)
        for s in ss:
            a=piece(h,s)
            # col flattening rows=(x,u), columns=(y,v).
            col=a.reshape((d,d,d,d)).transpose((0,2,1,3)).reshape((d*d,d*d))
            rec={'h':h,'s':s,'dimension':d,'rank_row_mod_p':rankmod(a),
                 'rank_col_mod_p':rankmod(col),
                 'row_factor_dimension':sum(len(parts(s+i)) for i in range(2*h+1)),
                 'col_factor_dimension':sum(len(parts(2*h-s-i)) for i in range(2*h+1))}
            results.append(rec); print(json.dumps(rec),flush=True)
            total=(total+a)%P
        if args.all_s:
            expected=np.zeros_like(total)
            for x in range(d):
                for y in range(d): expected[x*d+y,y*d+x]=factorial(h)%P
            if not np.array_equal(total,expected):
                raise AssertionError(f'crossing reconstruction failed h={h}')
        print(json.dumps({'h':h,'elapsed_seconds':time.time()-start,'cached_actions':action.cache_info().currsize}),flush=True)
        with output_path.open('w') as f: json.dump({'prime':P,'all_s':args.all_s,'results':results},f,indent=2)

if __name__=='__main__': main()

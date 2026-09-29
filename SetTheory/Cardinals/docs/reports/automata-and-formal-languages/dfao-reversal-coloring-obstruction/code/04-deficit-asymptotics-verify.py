#!/usr/bin/env python3
"""Exact finite certificate for binary DFAO reversal with three outputs.
Python 3.10+, standard library only. Checks remain enabled under python -O.
This is an arithmetic verifier, not a proof-assistant formalization.
"""
from __future__ import annotations
import argparse, json, math
from collections import deque
from functools import lru_cache
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)

@lru_cache(maxsize=None)
def orders(n: int, least: int = 1) -> frozenset[int]:
    """Orders from every nondecreasing partition of n into cycle lengths."""
    if n == 0:
        return frozenset((1,))
    return frozenset(math.lcm(t, o) for t in range(least, n+1)
                     for o in orders(n-t, t))

@lru_cache(maxsize=None)
def H(r: int, t: int) -> int:
    return max(math.lcm(t, o) for o in orders(r))

def nearest(n: int) -> tuple[int, int]:
    if n < 7:
        raise ValueError('The nearest admissible split is used only for n >= 7.')
    a = (n-1)//2 if n % 2 else n//2 - (1 if n % 4 == 0 else 2)
    return a, n-a

def p3(a: int, b: int) -> int:
    return 3*(2**a + 2**b - 2)

def candidates(n: int):
    # All three possible generator types. No accessibility assumption needed.
    yield dict(kind='two_permutations', gap=2*3**(n-1))
    yield dict(kind='two_singular', gap=4*3**(n-2)-1)
    for m in range(2, n+1):
        r = n-m
        for d in range(1, m):
            if m % d:
                continue
            length = m//d
            number = (2**length + (-1)**length*2)**d * 3**r
            period = H(r,m)
            yield dict(kind='same_cycle', m=m, d=d, r=r,
                       proper=number, period=period, gap=number-period)
    for a in range(1,n):
        for b in range(a,n-a+1):
            r = n-a-b
            d = math.gcd(a,b)
            number = p3(a//d,b//d)**d * 3**r
            period = (max(H(r,a),H(r,b)) if d == 1
                      else H(r,math.lcm(a,b)))
            yield dict(kind='cross_cycles', a=a,b=b,d=d,r=r,
                       proper=number,period=period,gap=number-period)

def witness(n: int, k: int = 3):
    """Holzer--Koenig/Krawetz generator convention; Davies output coloring."""
    a,b = nearest(n)
    if not 3 <= k < n:
        raise ValueError('Require 3 <= k < n.')
    p = tuple(list(range(1,a))+[0]+list(range(a+1,n))+[a])
    s = list(range(n)); s[0]=a; s[-1]=0
    if a > 2 and a % 2:
        s[1],s[2] = s[2],s[1]
    q = min(k-2,a)
    tau = list(range(q)) + [q-1]*(a-q)
    tau += list(range(q,k)) + [k-1]*(b-(k-q))
    require(len(tau)==n,'Invalid output coloring length')
    return p,tuple(s),tuple(tau)

def orbit(p,s,tau):
    seen={tau}; queue=deque((tau,))
    while queue:
        c=queue.popleft()
        for t in (p,s):
            v=tuple(c[q] for q in t)
            if v not in seen:
                seen.add(v); queue.append(v)
    return seen

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--max-n',type=int,default=31)
    parser.add_argument('--bfs-max-n',type=int,default=10)
    args=parser.parse_args()
    require(31 <= args.max_n <= 45,'Use 31 <= --max-n <= 45.')
    require(7 <= args.bfs_max_n <= 12,'Use 7 <= --bfs-max-n <= 12.')
    rows=[]; all_cases=[]
    for n in range(7,args.max_n+1):
        a,b=nearest(n); target=p3(a,b)-b
        cs=list(candidates(n))
        require(math.gcd(a,b)==1 and a>1,'Split is inadmissible')
        require(min(c['gap'] for c in cs)==target,f'Bound mismatch at n={n}')
        winners=[c for c in cs if c['gap']==target]
        # Stronger checked fact: the only minimizing graph parameters are (a,b).
        require(all(c['kind']=='cross_cycles' and c['r']==0
                    and (c['a'],c['b'])==(a,b) for c in winners),
                f'Unexpected minimizing graph at n={n}')
        row=dict(n=n,a=a,b=b,deficit=target,maximum=3**n-target,
                 candidates=len(cs),min_gap=min(c['gap'] for c in cs))
        rows.append(row); all_cases.append(dict(n=n,cases=cs))
        print(f"n={n:2d} split=({a},{b}) gap={target} cases={len(cs)} OK")
    bfs=[]
    for n in range(7,args.bfs_max_n+1):
        p,s,tau=witness(n)
        count=len(orbit(p,s,tau)); a,b=nearest(n)
        require(count==3**n-p3(a,b)+b,f'BFS mismatch n={n}')
        bfs.append(dict(n=n,p=p,s=s,tau=tau,states=count))
        print(f'BFS n={n}: {count} states OK')
    out=ROOT/'results';out.mkdir(exist_ok=True)
    (out/'finite_certificate.json').write_text(json.dumps(dict(rows=rows,all_cases=all_cases),indent=2)+'\n')
    (out/'bfs_checks.json').write_text(json.dumps(bfs,indent=2)+'\n')
    (out/'finite_table.tex').write_text('\n'.join(
        f"{r['n']} & ({r['a']},{r['b']}) & {r['deficit']:,} & {r['candidates']} \\\\" for r in rows)+'\n')
    summary=dict(finite_range=[7,args.max_n],rows=len(rows),
                 candidates=sum(r['candidates'] for r in rows),
                 bfs_range=[7,args.bfs_max_n],status='PASS',
                 boundary='Exact integer checks; not a formal proof-assistant certificate.')
    (out/'verification_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))
if __name__=='__main__':
    main()

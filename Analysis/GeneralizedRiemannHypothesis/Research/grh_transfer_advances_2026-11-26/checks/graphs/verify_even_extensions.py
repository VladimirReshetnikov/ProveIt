#!/usr/bin/env python3
"""Exact certificates for new optimal signings at n=34,36,38,42,44,46.
Python standard library only. No floating point decisions.
"""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json

CASES = {34:Q(281,100),36:Q(281,100),38:Q(281,100),42:Q(281,100),44:Q(703,250),46:Q(703,250)}

def extend(block,t,T):
    a,b,c=block
    return c-b*b/a, -1+b*t/a, T-1/a

def positive(block):
    a,b,c=block
    return a>0 and a*c>b*b

def path_frontiers(T,L):
    init=(T,Q(-1),T); frontier={(): (init,init)}; all_levels={0:set(frontier)};counts=[1]
    for k in range(1,L+1):
        children={}
        for w,(bminus,bplus) in frontier.items():
            for t in (-1,1):
                m,p=extend(bminus,t,T),extend(bplus,-t,T)
                if positive(m) and positive(p):children[w+(t,)]=(m,p)
        frontier=children;all_levels[k]=set(frontier);counts.append(len(frontier))
    return all_levels,counts

def canonical(word):
    return min(word[j:]+word[:j] for j in range(len(word)))

def cyclic_words(allowed,n):
    L=n-4;result=set()
    for pre in allowed:
        for suf in product((-1,1),repeat=4):
            w=pre+suf; ww=w+w
            if all(ww[j:j+L] in allowed for j in range(1,n)):
                result.add(canonical(w))
    return result

def integer_shift(word,alpha,T,side):
    n=len(word);a=[1]*(n-1)+[alpha];M=[[0]*n for _ in range(n)]
    for i in range(n):M[i][i]=T.numerator
    for i in range(n):
        for d,s in ((1,a[i]),(2,word[i]*a[i]*a[(i+1)%n])):
            j=(i+d)%n;M[i][j]=M[j][i]=side*T.denominator*s
    return M

def positive_definite(M):
    """Bareiss elimination, no row swaps: each pivot is a leading minor."""
    a=[row[:] for row in M];n=len(a);previous=1
    for k in range(n-1):
        pivot=a[k][k]
        if pivot<=0:return False
        for i in range(k+1,n):
            for j in range(k+1,n):
                num=a[i][j]*pivot-a[i][k]*a[k][j]
                a[i][j],rest=divmod(num,previous)
                assert rest==0
        previous=pivot
    return a[-1][-1]>0

def atan_partial(x,count):
    return sum(((-1)**k*x**(2*k+1)/Q(2*k+1) for k in range(count)),Q(0))

def cosine_upper_check(n,T):
    # Machin identity and the alternating-series bounds give this strict lower bound for pi.
    pi_lower=16*atan_partial(Q(1,5),10)-4*atan_partial(Q(1,239),3)
    assert pi_lower>Q(314159,100000)
    def cup(x):return 1-x*x/2+x**4/24
    theta=pi_lower/n
    assert 0 < 2*theta < 1
    assert 4*(cup(theta)**2+cup(2*theta)**2)<T*T
    assert T*T<8

def word_string(w):return ''.join('+' if t==1 else '-' for t in w)

def main():
    results=[]
    for T in sorted(set(CASES.values())):
        ns=[n for n in CASES if CASES[n]==T]
        levels,counts=path_frontiers(T,max(ns)-4)
        for n in ns:
            allowed=levels[n-4];necklaces=cyclic_words(allowed,n);passing=[]
            for w in sorted(necklaces):
                for alpha in (-1,1):
                    if all(positive_definite(integer_shift(w,alpha,T,side)) for side in (-1,1)):
                        passing.append((w,alpha))
            alt=canonical(tuple((-1)**i for i in range(n)))
            assert passing==[(alt,-1)],(n,passing)
            cosine_upper_check(n,T)
            r={'n':n,'threshold':str(T),'window_length':n-4,'prefix_counts':counts[:n-3],
               'cyclic_necklaces':len(necklaces),'passing':[{'word':word_string(w),'alpha':a} for w,a in passing],
               'all_minimizers':'two alternating triangle words; Hamilton product -1',
               'minimum':'2 sqrt(cos(pi/n)^2+cos(2*pi/n)^2)'}
            results.append(r)
            print(f'n={n}: {len(allowed)} exact windows, {len(necklaces)} cyclic necklaces; only alternating alpha=-1 passes {T}.',flush=True)
    out=Path(__file__).with_name('even_extension_certificate.json')
    out.write_text(json.dumps({'arithmetic':'exact rational and integer; no float tests','cases':sorted(results,key=lambda x:x['n'])},indent=2)+'\n')
    print('All six exact global optima certified.')

if __name__=='__main__':main()

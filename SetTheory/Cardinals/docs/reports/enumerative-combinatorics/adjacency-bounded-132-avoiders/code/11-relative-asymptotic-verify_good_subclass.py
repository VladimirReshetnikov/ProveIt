#!/usr/bin/env python3
"""Exact finite checks of the relaxed grammar and retained subclass.

Uses the credited model.py Catalan generator. No finite asymptotic extrapolation.
"""
from pathlib import Path
from math import comb
from collections import Counter
from functools import lru_cache
import hashlib,json
from model import avoiders,max_jump,catalans


def parse(p):
    ops=[]
    while len(p)>1:
        n=len(p);i=p.index(n)
        if i==n-1:
            ops.append(('A',()))
            p=p[:-1]
        else:
            right=p[i+1:];offset=len(right)
            ops.append(('R',tuple(x-offset for x in p[:i])))
            p=right
    return tuple(ops)


def build(ops):
    p=(1,)
    for typ,dec in reversed(ops):
        if typ=='A':p=p+(len(p)+1,)
        else:
            old=len(p);n=old+len(dec)+1
            p=tuple(x+old for x in dec)+(n,)+p
    return p


def member(p,M):
    while len(p)>1:
        n=len(p);i=p.index(n)
        if i==n-1:
            if n-p[-2]>M:return False
            p=p[:-1]
        else:
            if i+1>M:return False
            p=p[i+1:]
    return True


def good_dec(ops,D):
    return all(not dec or len(dec)+1-dec[0]<=D for typ,dec in ops if typ=='R')


def bad_run_start(ops,L):
    i=0
    while i<len(ops):
        if ops[i][0]!='A':i+=1;continue
        j=i
        while j<len(ops) and ops[j][0]=='A':j+=1
        if j-i>L:return i
        i=j
    return None


@lru_cache(None)
def c(k,D):
    if k==1:return 1
    return sum(j*comb(2*k-j-3,k-2)//(k-1) for j in range(1,min(D,k-1)+1))


def expected(n,M):
    C=catalans(M);u=[1]+[0]*(n-1)
    for j in range(1,n):
        u[j]=sum(C[k-1]*u[j-k] for k in range(1,min(M,j)+1))
    return sum(u[j]*u[n-1-j] for j in range(n))


def main():
    rows=[];parser=shape_checks=dec_checks=good_checks=deletion_checks=0
    digest=hashlib.sha256()
    for n in range(1,10):
        perms=avoiders(n)
        for p in perms:
            assert build(parse(p))==p;parser+=1
        for M in range(1,6):
            objects=[(p,parse(p)) for p in perms if member(p,M)]
            assert len(objects)==expected(n,M)
            shapes=Counter(tuple((typ,len(dec)+1 if typ=='R' else 1) for typ,dec in ops) for p,ops in objects)
            for signature,count in shapes.items():
                product=1
                for typ,k in signature:
                    if typ=='R':product*=comb(2*k-2,k-1)//k
                assert count==product;shape_checks+=1
            for D in range(1,4):
                restricted=Counter(tuple((typ,len(dec)+1 if typ=='R' else 1) for typ,dec in ops)
                                   for p,ops in objects if good_dec(ops,D))
                for sig in shapes:
                    product=1
                    for typ,k in sig:
                        if typ=='R':product*=c(k,D)
                    assert restricted[sig]==product;dec_checks+=1
                for L in range(1,4):
                    good=0;images=set();bad=0
                    for p,ops in objects:
                        start=bad_run_start(ops,L)
                        if start is None:
                            if good_dec(ops,D):
                                assert max_jump(p)<=M+D+L;good+=1;good_checks+=1
                        else:
                            reduced=ops[:start]+ops[start+L:]
                            assert reduced[start][0]=='A'
                            q=build(reduced)
                            assert len(q)==n-L and member(q,M)
                            image=(q,start)
                            assert image not in images
                            images.add(image)
                            restored=reduced[:start]+(('A',()),)*L+reduced[start:]
                            assert restored==ops
                            bad+=1;deletion_checks+=1
                    assert bad<=n*expected(n-L,M) if n>L else bad==0
                    row=dict(n=n,M=M,D=D,L=L,envelope=len(objects),good=good,bad_append=bad)
                    rows.append(row);digest.update((json.dumps(row,sort_keys=True)+'\n').encode())
    result=dict(status='passed',scope='Exact finite grammar regression, not an asymptotic proof',
                parser_roundtrips=parser,shape_factorizations=shape_checks,
                restricted_decoration_factorizations=dec_checks,good_cap_checks=good_checks,
                marked_deletion_checks=deletion_checks,row_count=len(rows),
                row_sha256=digest.hexdigest(),rows=rows)
    Path(__file__).with_name('good_subclass_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='rows'},sort_keys=True))

if __name__=='__main__':main()

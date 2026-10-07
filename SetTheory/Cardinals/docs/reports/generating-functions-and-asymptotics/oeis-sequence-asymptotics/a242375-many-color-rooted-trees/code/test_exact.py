#!/usr/bin/env python3
"""Independent exact checks and CLI guard regressions. Standard library only."""
import collections
from fractions import Fraction
import hashlib
import heapq
import itertools
import json
import math
import os
from pathlib import Path
import subprocess
import sys
import colored_trees as ct
from certify_bounds import verify


def require(ok, message):
    if not ok:
        raise ArithmeticError(message)


def euler_counts(N,q,kind):
    """Rebuild Euler products, independently of the divisor recurrence."""
    A=[0,1]
    for n in range(2,N+1):
        coefficients=[1]+[0]*(n-1)
        for m in range(1,n):
            types=q*A[m]
            signed=kind in ('identity','B')
            if m==1 and kind in ('zero','B'):
                # q individual leaf factors, independent of logarithmic recurrence.
                factor=[1,1] if kind=='zero' else [1,1,1]
                for _ in range(q):
                    new=[0]*n
                    for i,v in enumerate(coefficients):
                        for k,f in enumerate(factor):
                            if i+k<n: new[i+k]+=v*f
                    coefficients=new
                continue
            terms=[]
            for k in range((n-1)//m+1):
                terms.append(math.comb(types,k) if signed and k<=types else
                             0 if signed else math.comb(types+k-1,k))
            new=[0]*n
            for i,v in enumerate(coefficients):
                for k,f in enumerate(terms):
                    if i+m*k<n: new[i+m*k]+=v*f
            coefficients=new
        A.append(coefficients[n-1])
    return A


def rooted_children(n,seq):
    if n==1: return [[]],[0]
    degree=[1]*n
    for x in seq: degree[x]+=1
    heap=[i for i in range(n) if degree[i]==1];heapq.heapify(heap)
    adj=[[] for _ in range(n)]
    for x in seq:
        leaf=heapq.heappop(heap);adj[leaf].append(x);adj[x].append(leaf)
        degree[leaf]-=1;degree[x]-=1
        if degree[x]==1: heapq.heappush(heap,x)
    a,b=heap;adj[a].append(b);adj[b].append(a)
    children=[[] for _ in range(n)];order=[0];parent=[-1]*n
    for v in order:
        for w in adj[v]:
            if w!=parent[v]: parent[w]=v;children[v].append(w);order.append(w)
    return children,order


def canonical(children,order,colors):
    codes=[None]*len(order)
    for v in reversed(order):
        codes[v]=tuple(sorted((colors[w],codes[w]) for w in children[v]))
    return codes[0]


def stats(code):
    multiplicities=collections.Counter(code)
    J,aut,good=0,1,True
    for (_,sub),m in multiplicities.items():
        j,a,b=stats(sub)
        J+=m*j+(m*(m-1)//2 if not sub else 0)
        aut*=a**m*math.factorial(m)
        good=good and b and m <= (2 if not sub else 1)
    return J,aut,good


def run():
    initial_limit=sys.get_int_max_str_digits() if hasattr(sys,'get_int_max_str_digits') else None
    rows=[]
    for q in (1,2,3,5,40):
        for kind in ct.KINDS:
            require(ct.counts(11,q,kind)==euler_counts(11,q,kind),f'Euler mismatch {q} {kind}')
    for n in range(1,7):
        shapes=[rooted_children(n,seq) for seq in itertools.product(range(n),repeat=max(0,n-2))]
        for q in (1,2,3):
            objects=collections.Counter()
            for ch,order in shapes:
                for colors in itertools.product(range(q),repeat=n-1):
                    objects[canonical(ch,order,(-1,)+colors)]+=1
            allhist=collections.Counter();bhist=collections.Counter();identity=zero=0;weightedJ=0
            for ob,mult in objects.items():
                J,aut,good=stats(ob)
                allhist[J]+=1;weightedJ+=mult*J
                require(mult*aut==math.factorial(n-1),'orbit stabilizer')
                identity+=aut==1;zero+=J==0
                if good:
                    bhist[J]+=1
                    require(aut==2**J,'B group order')
            require(dict(allhist)==ct.marked_counts(n,q)[n],'marked all polynomial')
            prefix,total=ct.marked_prefix(n,q,16)
            require({k:v for k,v in enumerate(prefix) if v}==dict(allhist) and total==len(objects),'truncated marked polynomial')
            require(dict(bhist)==ct.marked_counts(n,q,'B')[n],'marked B polynomial')
            for kind,value in [('all',len(objects)),('identity',identity),('zero',zero),('B',sum(bhist.values()))]:
                require(ct.counts(n,q,kind)[n]==value,'exact object count')
            mean=Fraction(weightedJ,sum(objects.values()))
            expected=Fraction((n-1)*(n-2)**(n-2),2*q*n**(n-2)) if n>=3 else Fraction(0)
            require(mean==expected,'labeled exact mean')
            rows.append({'N':n,'q':q,'classes':len(objects),'identity':identity,'J_zero':zero,'B':sum(bhist.values()),'labeled_mean':str(mean),'marked_histogram':dict(sorted(allhist.items()))})
    data=json.loads((Path(__file__).resolve().parents[1]/'data'/'oeis_diagonal_prefix.json').read_text())
    for kind in ('all','identity'):
        for n,text in enumerate(data[kind]):
            require(ct.decimal(ct.diagonal(n,kind))==text,'OEIS prefix')
    # Exact inverses: verify least threshold, including initial repeated 1 values.
    for kind in ('all','identity'):
        for y in (1,2,5,20,100,10000):
            index=ct.diagonal_threshold(y,20,kind)
            require(index is not None and ct.diagonal(index,kind)>=y,'inverse upper')
            require(index==0 or ct.diagonal(index-1,kind)<y,'inverse least')
    require(ct.diagonal_threshold(10**100,1) is None,'bounded inverse absence')
    palette=ct.palette_threshold(10,9,10,100)
    require(palette is not None,'palette bounded existence')
    for q in range(1,palette+1):
        success=10*ct.counts(10,q,'identity')[-1]>=9*ct.counts(10,q)[-1]
        require(success==(q==palette),'palette global scan')
    # Input checks must survive -O. No assert statement is used.
    invalid=[lambda:ct.counts(True,1),lambda:ct.counts(0,1),lambda:ct.counts(2,0),
             lambda:ct.counts(2,1,'bad'),lambda:ct.counts(ct.MAX_N+1,1),
             lambda:ct.parse_target('9'*601),lambda:ct.parse_target('0'),
             lambda:ct.parse_target('１２'),lambda:ct.parse_target('-1'),
             lambda:ct.marked_counts(13,1),lambda:ct.palette_threshold(2,1,1),
             lambda:ct.palette_threshold(2000,1,2,100)]
    for operation in invalid:
        try: operation()
        except ValueError: pass
        else: raise ArithmeticError('input guard missing')
    # Real large-output CLI regression under the minimum CPython decimal limit.
    expected=ct.decimal(ct.counts(640,640)[-1])
    require(len(expected)>640,'test is not a large decimal')
    env=dict(os.environ,PYTHONINTMAXSTRDIGITS='640')
    cli=Path(ct.__file__).resolve()
    for flags in ([],['-O']):
        result=subprocess.run([sys.executable,*flags,str(cli),'count','640','640'],env=env,capture_output=True,text=True,check=True)
        require(result.stdout.rstrip('\n')==expected,'large stdout mismatch')
        bad=subprocess.run([sys.executable,*flags,str(cli),'inverse','9'*641],env=env,capture_output=True,text=True)
        require(bad.returncode!=0 and '600 ASCII' in bad.stderr,'CLI threshold guard')
    require(initial_limit==(sys.get_int_max_str_digits() if hasattr(sys,'get_int_max_str_digits') else None),'global integer setting changed')
    verify()
    return {'status':'pass','arithmetic':'exact; no float tolerances','Euler_product_cases':20,'Euler_product_max_N':11,
            'Pruefer_quotient_cases':rows,'OEIS_prefix_n':'0..35, both diagonals',
            'large_cli':{'N':640,'q':640,'decimal_digits':len(expected),'sha256':hashlib.sha256(expected.encode()).hexdigest(),'decimal_guard':640,'modes':['normal','optimized']},
            'input_guard_cases':len(invalid),'exact_palette_N10_target_9over10':palette,
            'global_settings':'integer conversion setting preserved','analytic_bounds':'exact rational certificates passed'}


if __name__=='__main__':
    print(json.dumps(run(),indent=2,sort_keys=True))

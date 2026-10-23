"""Coordinate shift and quadratic coefficient weights.
Adapted from the incoming Selective Quadratic package's verify_selective.py.
Exact arithmetic only; the independent auditor reconstructs the result separately.
"""
import collections,itertools,math

def require(ok,message):
    if not ok:raise ValueError(message)

def shifted_source(source):
    n=len(source['variables']);blocks={}
    for eq in source['equations']:
        shifted=collections.defaultdict(int)
        for row in eq['terms']:
            powers=row['powers'];supp=[i for i,e in enumerate(powers[:n]) if e]
            for ks in itertools.product(*(range(powers[i]+1) for i in supp)):
                mon=[0]*n+powers[n:];c=row['coefficient']
                for i,k in zip(supp,ks):mon[i]=k;c*=math.comb(powers[i],k)
                shifted[tuple(mon)]+=c
        terms=collections.defaultdict(dict)
        for mon,c in shifted.items():
            if not c:continue
            alpha=mon[:n];require(sum(alpha)<=2,'not quadratic')
            padded=[0]*(2-sum(alpha))+[i+1 for i,e in enumerate(alpha) for _ in range(e)]
            fac=math.factorial(2-sum(alpha))*math.prod(math.factorial(e) for e in alpha)
            terms[tuple(padded)][mon[n:]]=c*fac
        blocks[eq['number']]=dict(terms)
    return blocks

#!/usr/bin/env python3
"""Illustrative numerical samples, NOT certificates of infinite inequalities.
Requires SymPy. Factorization and discriminants are exact; log sums are floats.
"""
import argparse, csv, math, warnings, sys
import sympy as sp
from sympy.utilities.exceptions import SymPyDeprecationWarning
warnings.filterwarnings('ignore', category=SymPyDeprecationWarning)
X=sp.Symbol('X')
DATA=[('S4',X**4-X-1,-283,{(1,1,1,1):17,(2,2):-3,(1,3):-1}),('S5',X**5-X-1,2869,{(1,1,1,1,1):133,(1,2,2):-3,(1,1,3):-2,(5,):-2}),('PSL2(7)',X**7-7*X+3,3**8*7**8,{(1,)*7:21,(1,1,1,2,2):-1})]
def factor_type(f,p):
    return tuple(sorted(int(sp.degree(g,X)) for g,m in sp.factor_list(f,modulus=p)[1] for _ in range(m)))
def main():
    parser=argparse.ArgumentParser(); parser.add_argument('--scales',type=int,nargs='+',default=[100,1000,10000]); a=parser.parse_args(); scales=sorted(set(a.scales))
    assert all(x>=2 for x in scales)
    assert factor_type(DATA[0][1],2)==(4,) and factor_type(DATA[0][1],7)==(1,3) and factor_type(DATA[0][1],17)==(1,1,2)
    assert factor_type(DATA[1][1],2)==(2,3) and factor_type(DATA[1][1],3)==(5,)
    writer=csv.writer(sys.stdout,lineterminator='\n'); writer.writerow(['group','x','weighted_primes_positive','weighted_primes_negative','uncentered_smoothed_sum'])
    for group,f,disc,weights in DATA:
        assert sp.discriminant(f,X)==disc
        pp=[]
        for p in sp.primerange(2,max(scales)+1):
            if disc%p==0: continue
            typ=factor_type(f,p); w=weights.get(typ,0)
            if w:pp.append((int(p),w))
        for x in scales:
            pairs=[(p,w) for p,w in pp if p<=x]
            a=math.fsum(w*math.log(p)*(1/p-1/x) for p,w in pairs)
            writer.writerow([group,x,sum(w>0 for p,w in pairs),sum(w<0 for p,w in pairs),f'{a:.12f}'])
if __name__=='__main__':main()

"""Closed-inventory integrity and finite mathematical checks. Not a proof checker."""
import sys
sys.dont_write_bytecode=True
import argparse, hashlib, json, subprocess, stat
from pathlib import Path
import sympy as S
from itertools import combinations
from exact import exact_values, exact_selected, independent_exact, list_sets, require_nonnegative
from formulas import coefficient_formulas
from derive_general import derive

FILES={'Report132.tex','Report132.pdf','README.md','requirements.txt','sources.md','fixtures.json',
       'diagnostics_3200.json','derive.py','derive_general.py','exact.py','formulas.py','validate.py',
       'check.py','build.py','package.py','qa.py','safe_output.py','MANIFEST.json'}
ROOT=Path(__file__).resolve().parent

def require(condition,message):
    if not condition:
        raise RuntimeError(message)

def integrity():
    entries=list(ROOT.iterdir())
    actual={p.name for p in entries}
    require(actual==FILES,'inventory mismatch: '+str(sorted(actual^FILES)))
    require(all(stat.S_ISREG(p.lstat().st_mode) for p in entries),'nonregular entry in bundle')
    hashes=json.loads((ROOT/'MANIFEST.json').read_text())
    require(set(hashes)==FILES-{'MANIFEST.json'},'manifest inventory mismatch')
    for name,digest in hashes.items():
        require(hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest,'hash mismatch: '+name)

def brute_count(n):
    """Reject each induced five-vertex path, using the matrix support only."""
    count=0
    for mask in range(1<<(n*n)):
        rows=[[(mask>>(r*n+c))&1 for c in range(n)] for r in range(n)]
        bad=False
        for transposed in [False,True]:
            a=list(map(list,zip(*rows))) if transposed else rows
            for rr in combinations(range(n),2):
                for cc in combinations(range(n),3):
                    p=[a[rr[0]][c] for c in cc];q=[a[rr[1]][c] for c in cc]
                    if sum(p)==sum(q)==2 and sum(x*y for x,y in zip(p,q))==1:
                        bad=True;break
                if bad:break
            if bad:break
        count+=not bad
    return count

def inverse_checks():
    h,beta,J,k,c1=S.symbols('h beta J k c1', nonzero=True)
    a=-beta/(2*h)
    D=(J/4-k)/(2*h)+beta**2/(8*h**2)-beta**2/(8*h**3)
    e=-(c1+beta*D*(S.Rational(1,2)-1/h)+beta/(8*h)+beta**3/(24*h**3)-beta**3/(32*h**2))/(2*h)
    residuals=[2*h*a+beta,2*h*D+a*a+beta*a/2-J/4+k,
               2*h*e+2*a*D-a**3/3+beta*D/2-beta*a*a/8-a/4+c1]
    for j,residual in enumerate(residuals):
        require(S.factor(residual)==0,'inverse cancellation '+str(j))

def finite_checks():
    fixture=json.loads((ROOT/'fixtures.json').read_text())
    values=exact_values(15)
    require(values==[int(x) for x in fixture['a_n']],'exact fixture mismatch')
    require(values[:4]==[brute_count(n) for n in range(4)],'exhaustive induced-P5 count mismatch')
    require(values==[independent_exact(n) for n in range(16)],'independent finite-difference count mismatch')
    require(all(values[n+1]>=2*values[n] for n in range(15)),'small monotonicity check')
    for bad in [-1,True,1.5]:
        try:require_nonnegative(bad)
        except ValueError:pass
        else:raise RuntimeError('invalid dimension accepted')
    for bad in [[1,True],[True,1],[1,1.0],[1.0,1]]:
        try:exact_selected(2,bad)
        except ValueError:pass
        else:raise RuntimeError('mixed invalid selected dimension accepted')
    d0=derive(0)
    require(d0['c']==[1] and len(d0['P'])==1,'zero-order extraction')
    d=derive(2); z,U=d['z'],d['U']
    L=8*z*z
    require(S.factor(d['A']-16*z)==0 and S.factor(d['B']-(1-L))==0,'quadratic constants')
    require(S.factor(d['gamma']-(2*L-S.Rational(5,8)+1/(8*L)))==0,'constant exponent')
    for j,c in enumerate(coefficient_formulas(L),1):
        require(S.simplify(d['c'][j]-c)==0,'symbolic c'+str(j)+' mismatch')
    for j,P in enumerate(d['P']):
        require(S.expand(P.subs(U,-U)-(-1)**j*P)==0,'phase parity '+str(j))
    for j,Q in enumerate(d['Q']):
        require(S.expand(Q.subs(U,-U)-(-1)**j*Q)==0,'exponential parity '+str(j))
    inverse_checks()
    require('167' in (ROOT/'Report132.tex').read_text(),'article coefficient absent')
    print('PASS: exact fixtures 0..15; exhaustive counts 0..3; independent sum; zero order; c1/c2; parity; inverse cancellations')

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--integrity-only',action='store_true')
    parser.add_argument('--finite-only',action='store_true',help='development use; skips the integrity check')
    args=parser.parse_args()
    require(not(args.integrity_only and args.finite_only),'conflicting check modes')
    if not args.finite_only:integrity();print('PASS: closed inventory and SHA-256 integrity')
    if not args.integrity_only:finite_checks()
if __name__=='__main__':main()

"""Independent symbolic MATRIX compiler and real-root checks using SymPy.

Production code requires only Python's standard library. SymPy is used solely
as an independent validation implementation and is not a runtime dependency.
"""
import json,platform,random,sys
from pathlib import Path
import sympy as sp
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'code'))
from su2budget.slp import from_words
from su2budget.dihedral import solve
from su2budget.univariate import positive_roots


def matrix_check(pairs):
    t=sp.Symbol('t',real=True);den=1+t*t
    A=sp.Matrix([[sp.I,0],[0,-sp.I]])
    B=sp.Matrix([[sp.I*(1-t*t),2*t],[-2*t,-sp.I*(1-t*t)]])
    residual=[]
    def word(w):
        M=sp.eye(2);degree=0
        for x in w:
            N=A if abs(x)==1 else B
            M=(M*(N if x>0 else -N)).applyfunc(sp.expand)
            degree+=int(abs(x)==2)
        return M,degree
    for u,v in pairs:
        U,e=word(u);V,f=word(v);d=max(e,f)
        M=U*den**(d-e)-V*den**(d-f)
        for entry in M:
            re,im=sp.expand(entry).as_real_imag()
            residual.extend([sp.Poly(re,t),sp.Poly(im,t)])
    nonzero=[f for f in residual if not f.is_zero]
    if not nonzero:return None
    g=nonzero[0]
    for f in nonzero[1:]:g=sp.gcd(g,f)
    while g.degree()>0 and g.eval(0)==0:g=sp.div(g,sp.Poly(t,t))[0]
    return int(g.count_roots(0,sp.oo))


def main():
    rng=random.Random(20261008);records=[]
    for i in range(100):
        pairs=[([rng.choice((-2,-1,1,2)) for _ in range(rng.randrange(0,9))],
                [rng.choice((-2,-1,1,2)) for _ in range(rng.randrange(0,9))])
               for _ in range(rng.randrange(1,3))]
        p=from_words(2,pairs,meridians=True,label='synthetic matrix comparison, not a knot claim')
        d=solve(p);roots=matrix_check(pairs)
        expected='EXISTS' if roots is None or roots>0 else 'NONE'
        assert d['status']==expected,(pairs,d,roots)
        if 'count' in d:assert (None if d['count']=='continuum' else d['count'])==roots
        records.append(dict(index=i,pairs=pairs,status=expected,positive_roots=roots))
    # Nonrandom positive-dimensional/discrete examples supplement random groups,
    # which are mostly inconsistent in the traceless slice.
    for m in range(0,15):
        pairs=[([1,2]*m+[1],[2]+[1,2]*m)]
        p=from_words(2,pairs,meridians=True,label=f'two-strand torus relation m={m}')
        d=solve(p);roots=matrix_check(pairs)
        assert roots==m
        assert d.get('count')==m
        records.append(dict(index=100+m,pairs=pairs,status=d['status'],positive_roots=roots))
    t=sp.Symbol('t')
    for i in range(200):
        coefficients=[rng.randrange(-9,10) for _ in range(rng.randrange(1,13))]
        if not any(coefficients):coefficients=[1]
        f=sp.Poly(sum(c*t**j for j,c in enumerate(coefficients)),t)
        while f.degree()>0 and f.eval(0)==0:f=sp.div(f,sp.Poly(t,t))[0]
        expected=int(f.count_roots(0,sp.oo))
        assert positive_roots(coefficients)['count']==expected
    output=dict(python=platform.python_version(),sympy=sp.__version__,seed=20261008,
                independently_compiled_matrix_presentations=len(records),
                independent_sturm_comparisons=200,records=records,status='PASS')
    path=Path(__file__).resolve().parents[1]/'data'/'independent_validation.json'
    path.write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({k:v for k,v in output.items() if k!='records'},indent=2))

if __name__=='__main__':main()

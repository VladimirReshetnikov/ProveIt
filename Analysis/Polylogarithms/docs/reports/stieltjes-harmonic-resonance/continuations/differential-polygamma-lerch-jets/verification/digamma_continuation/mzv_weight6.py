from collections import Counter
from functools import lru_cache
from itertools import product
from pathlib import Path
import sympy as sp
from compute_appell import compute,nice,z,stuffle,even_reduce

def comps(n):
    if n==0:return [()]
    return [(k,)+w for k in range(1,n+1) for w in comps(n-k)]
def admissible(n):return [w for w in comps(n) if w[0]>=2]
def code(w):return tuple(c for n in w for c in (0,)*(n-1)+(1,))
def decode(w):
    out=[];n=1
    for c in w:
        if c==0:n+=1
        else:out.append(n);n=1
    assert n==1
    return tuple(out)
def dual(w):return decode(tuple(1-x for x in code(w)[::-1]))
@lru_cache(None)
def shuffle(a,b):
    if not a:return {b:1}
    if not b:return {a:1}
    out=Counter()
    for w,c in shuffle(a[1:],b).items():out[(a[0],)+w]+=c
    for w,c in shuffle(a,b[1:]).items():out[(b[0],)+w]+=c
    return dict(out)
def shuffle_indices(a,b):return {decode(w):c for w,c in shuffle(code(a),code(b)).items()}
def table6():
    words=admissible(6)
    symbols={w:sp.Symbol('Z'+'_'.join(map(str,w))) for w in words}
    zz=lambda w: symbols[w]
    known={(2,):z[2],(3,):z[3],(4,):z[4],(2,1):z[3],(3,1):z[4]/4,(2,2):3*z[4]/4,(2,1,1):z[4]}
    eq=[];labels=[]
    def add(label,d,rhs=0):
        eq.append(sp.expand(sum(c*zz(w) for w,c in d.items())-rhs));labels.append(label)
    add('single',{(6,):1},z[6])
    for w in words:
        add('duality '+str(w),Counter({w:1})-Counter()) if False else None
        row=Counter();row[w]+=1;row[dual(w)]-=1
        add('duality '+str(w),row)
    for k in [2,3,4]:
        for a in admissible(k):
            for b in admissible(6-k):
                value=known[a]*known[b]
                add('stuffle '+str((a,b)),stuffle(a,b),value)
                add('shuffle '+str((a,b)),shuffle_indices(a,b),value)
    for b in admissible(5):
        row=Counter(stuffle((1,),b))
        for w,c in shuffle_indices((1,),b).items():row[w]-=c
        row={w:c for w,c in row.items() if c}
        assert all(w[0]>=2 for w in row)
        add('regularized '+str(b),row)
    eq=[sp.expand(x).subs(z[2]*z[4],sp.Rational(7,4)*z[6]) for x in eq]
    mat,vec=sp.linear_eq_to_matrix(eq,list(symbols.values()))
    sol=sp.linsolve((mat,vec));soltuple=next(iter(sol))
    assert not set(symbols.values()).intersection(set().union(*(x.free_symbols for x in soltuple)))
    vals=dict(zip(words,soltuple))
    print('rank',mat.rank(),'rows',len(eq),'columns',len(words))
    for w,c in vals.items():print(w,sp.factor(c))
    expr=sp.expand(sum(nice(c)*(vals[w] if sum(w)==6 else known[w]) for w,c in compute(7)['Jwords'].items()))
    expr=sp.expand(expr.subs(z[2]*z[4],sp.Rational(7,4)*z[6]))
    print('J7=',expr)
    selected=list(mat.T.rref()[1])
    square=mat[selected,:]
    inverse=square.inv()
    assert inverse*square==sp.eye(len(words))
    assert inverse*vec[selected,:]==sp.Matrix(soltuple)
    import json
    Path(__file__).with_name('mzv6_relations.json').write_text(json.dumps({'words':words,'labels':labels,'matrix':[list(map(str,row)) for row in mat.tolist()],'rhs':list(map(str,vec)),'selected_rows':selected,'selected_inverse':[list(map(str,row)) for row in inverse.tolist()],'solutions':{str(w):str(c) for w,c in vals.items()},'J7':str(expr)},indent=2))
    return vals
if __name__=='__main__':table6()

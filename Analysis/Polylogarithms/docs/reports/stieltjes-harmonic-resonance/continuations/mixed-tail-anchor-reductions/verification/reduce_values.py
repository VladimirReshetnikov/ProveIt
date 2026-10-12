"""Exact rational research routines. See article.tex for conventions and proofs.

MZV words use descending indices. No numerical period-independence assumption
is used. The compiler accepts integer orders at least two.
"""
from double_shuffle import *
base_by_weight={2:[Z((2,))],3:[Z((3,))],4:[Z((4,))],5:[Z((5,)),Z((2,))*Z((3,))],6:[Z((6,)),Z((3,))**2],7:[Z((7,)),Z((2,))*Z((5,)),Z((3,))*Z((4,))],8:[Z((8,)),Z((3,))*Z((5,)),Z((2,))*Z((3,))**2,Z((5,3))]}
base_by_weight[9]=[Z((9,)),Z((2,))*Z((7,)),Z((4,))*Z((5,)),Z((6,))*Z((3,)),Z((3,))**3]
@lru_cache(None)
def reducer(weight):
    words,R,labels=relations(weight)
    Bs=S.Matrix.vstack(*(vector(e,words) for e in base_by_weight[weight]))
    mat=R.col_join(Bs);piv=mat.T.rref()[1];chosen=mat[list(piv),:]
    assert chosen.rows==chosen.cols,(weight,chosen.shape)
    inv=chosen.T.inv(method='DM')
    return words,R,labels,piv,inv

def reduce(expr):
    e=linearize(expr)
    unknown=[z for z in e.free_symbols if not str(z).startswith('Z_')]
    if unknown:raise ValueError(f'Unsupported non-MZV symbols: {unknown}')
    out=e.subs({z:0 for z in e.free_symbols})
    for weight in sorted({sum(map(int,str(z)[2:].split('_'))) for z in e.free_symbols if str(z).startswith('Z_')}):
      if weight not in base_by_weight:raise ValueError(f"Unsupported weight {weight}")
      syms=[z for z in e.free_symbols if str(z).startswith('Z_') and sum(map(int,str(z)[2:].split('_')))==weight]
      if not syms:continue
      sub=sum(e.coeff(z)*z for z in syms)
      words,R,labels,piv,inv=reducer(weight)
      cs=inv*vector(sub,words).T
      out+=sum(c*base_by_weight[weight][i-R.rows] for i,c in zip(piv,cs) if i>=R.rows)
    return S.expand(out)


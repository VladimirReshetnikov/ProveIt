#!/usr/bin/env python3
"""Independent finite premises for two full-HC countermodels.

The unbounded HC transfer is proved in formalism_results.tex.
These exhaustive finite checks do not replace that mathematical argument.
"""
import argparse,json
from itertools import product
from pathlib import Path

M4=((3,3,3,3),(3,3,2,3),(3,1,3,3),(0,0,0,3))
M5=((4,4,4,4,4),(4,4,3,4,4),(4,4,4,1,4),(4,2,4,4,4),(0,0,0,0,4))

def verify(M,restrictions,include_k):
    n=len(M);D=n-1;V=range(n);I=lambda a,b:M[a][b]
    N=lambda a:I(a,0)
    Q=lambda xs:D if all(a==D for a in xs) else 0
    L=lambda a,b,c,u:I(I(I(c,u),a),I(I(a,c),I(b,c)))
    P=lambda a,b:I(I(I(a,b),a),a)
    K=lambda a,b:I(a,I(b,a))
    terms={'F':lambda a,b,c:0,'T':lambda a,b,c:D,'A':lambda a,b,c:a,'B':lambda a,b,c:b,'C':lambda a,b,c:c}
    assert all(M[0][a]==D for a in V)
    assert all(M[a][a]==D for a in V)
    assert all(M[D][a]!=D or a==D for a in V)
    assert M[1][2]!=D
    assert all(I(a,b) in (0,D) for a in V for b in (0,D))
    assert all((I(a,b)==D)==(a!=D or b==D) for a in V for b in (0,D))
    assert all(N(a)==(0 if a==D else D) for a in V)
    assert all(N(I(a,N(b)))==(D if a==b==D else 0) for a,b in product(V,repeat=2))
    assert all(P(a,b)==D for a,b in product(V,repeat=2))
    assert all(I(N(N(a)),a)==D for a in V)
    assert all(I(I(N(a),a),a)==D for a in V)
    for key in restrictions:
        assert all(L(a,b,c,terms[key](a,b,c))==D for a,b,c in product(V,repeat=3)),key
    kfail=[[a,b]for a,b in product(V,repeat=2) if K(a,b)!=D]
    if include_k:assert not kfail
    if n==5:assert kfail==[[1,3],[2,1],[3,2]]
    omitted=[key for key in terms if key not in restrictions]
    omitted_failures={key:[[a,b,c] for a,b,c in product(V,repeat=3)
                          if L(a,b,c,terms[key](a,b,c))!=D] for key in omitted}
    assert all(omitted_failures.values())
    # Finite diagnostics for the general MP-based proof of normality.
    distribution=0
    for length in (1,2,3):
        vectors=list(product(V,repeat=length))
        for aa,bb in product(vectors,repeat=2):
            assert I(Q([I(a,b)for a,b in zip(aa,bb)]),I(Q(aa),Q(bb)))==D
            distribution+=1
    full_failures=[[a,b,c,u,L(a,b,c,u)]for a,b,c,u in product(V,repeat=4)if L(a,b,c,u)!=D]
    assert full_failures
    return {'status':'FINITE_PREMISES_PASS','matrix':[list(r)for r in M],
      'designated':D,'falsum':0,'restrictions':restrictions,'restricted_rho8_checks':len(restrictions)*n**3,
      'peirce_checks':n**2,'extra_valid_schemes':['identity','ex_falso','double_negation_elimination','Clavius']+(['K'] if not kfail else []),
      'K_failures':kfail,'color_separation_entry':[1,2,M[1][2]],
      'omitted_restriction_failures':omitted_failures,
      'distribution_vector_checks_lengths_1_2_3':distribution,'full_rho8_failures':full_failures,
      'unbounded_step':'HC coloring and countable witness closure; see the self-contained proof in formalism_results.tex.'}

def main():
    if not __debug__:
        raise SystemExit('Run with assertions enabled; omit -O and -OO.')
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path);args=ap.parse_args()
    result={'scope':'Sound HC models for complete retained native calculi, not merely propositional counterexamples.',
      'four_value':verify(M4,['F','T','A','C'],True),
      'five_value':verify(M5,['F','T','B','C'],False)}
    raw=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.out:args.out.write_text(raw)
    print(raw,end='')

if __name__=='__main__':main()

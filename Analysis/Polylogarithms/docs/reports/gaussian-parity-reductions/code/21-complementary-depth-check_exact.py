"""Rebuild exact certificates and validate independent constructions.
Run from any directory: python code/check_exact.py
"""
from __future__ import annotations
from collections import Counter
from fractions import Fraction
from itertools import product
from pathlib import Path
from math import comb, factorial
import csv, json
from polylog_words import *

ROOT = Path(__file__).resolve().parents[1]

def enc(terms):
    return [dict(log_power=j, q_indices=list(S), zeta_indices=list(T),
                 numerator=c.numerator, denominator=c.denominator)
            for (j,S,T),c in sorted(terms.items())]


def main():
    counts = Counter()
    # Normalize -> re-expand in the free shuffle algebra: exact identity.
    for n in range(9):
        for word in product((0,1), repeat=n):
            expanded = Counter()
            for (j,u),c in normalize_trailing_zeros(word).items():
                for v,d in shuffle(u,(0,)*j).items():
                    expanded[v] += c * factorial(j) * d
            expanded = {k:v for k,v in expanded.items() if v}
            assert expanded == {word:1}, (word,expanded)
            counts['trailing_zero_reexpansions'] += 1
    # An independent closed-form calculation vs. the general word algorithm.
    onezero=[]
    for weight in range(2,13):
        for a in range(weight-1):
            b=weight-2-a
            word=(1,)*a+(0,)+(1,)*(b+1)
            red=complement_reduce(word)
            assert red==one_zero_formula(a,b)
            counts['one_zero_independent_matches']+=1
            onezero.append(dict(weight=weight,a=a,b=b,terms=enc(red)))
    twozero=[]
    for weight in range(3,13):
        word=(0,0)+(1,)*(weight-2)
        red=complement_reduce(word)
        assert red==two_zero_height_one(weight)
        counts['two_zero_independent_matches']+=1
        twozero.append(dict(weight=weight,terms=enc(red)))
    # Every admissible word through weight 8 with depth > weight/2.
    catalogue=[]
    for weight in range(1,9):
        for word in admissible_words(weight):
            depth=sum(word)
            if 2*depth<=weight:continue
            red=complement_reduce(word)
            catalogue.append(dict(word=''.join(map(str,word)),
                                  indices=list(word_to_indices(word)),weight=weight,
                                  depth=depth,zero_count=weight-depth,terms=enc(red)))
            counts['high_depth_catalogue_entries']+=1
            counts['high_depth_catalogue_terms']+=len(red)
    # Triangular shuffle basis certificates. All admissible words, weight<=10.
    # No assumptions about numerical independence are involved.
    rank_table=[];weight6=[]
    for weight in range(1,11):
        for depth in range(1,weight+1):
            words=list(admissible_words(weight,depth))
            L=sum(is_lyndon(word) for word in words)
            assert L==lyndon_count(weight,depth)
            for word in words:
                factors=lyndon_factorization(word)
                assert all(f[-1]==1 for f in factors)
                poly=shuffle_many(factors)
                expected=1
                for mult in Counter(factors).values():expected*=factorial(mult)
                assert poly[word]==expected
                assert max(poly)==word
                counts['lyndon_triangular_checks']+=1
                if weight==6 and depth==3:
                    weight6.append(dict(word=''.join(map(str,word)),
                        indices=list(word_to_indices(word)),lyndon=is_lyndon(word),
                        factors=[''.join(map(str,f)) for f in factors],
                        expansion=[dict(word=''.join(map(str,v)),coefficient=c)
                                   for v,c in sorted(poly.items())]))
            rank_table.append(dict(weight=weight,depth=depth,coordinates=len(words),
                                   quotient_dimension=L,product_rank=len(words)-L))
    for name,obj in [('one_zero.json',onezero),('two_zero_height_one.json',twozero),
                     ('complementary_depth_catalogue.json',catalogue),
                     ('weight6_triples_shuffle.json',weight6)]:
        (ROOT/'certificates'/name).write_text(json.dumps(obj,indent=2)+'\n')
    with (ROOT/'tables'/'shuffle_ranks.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(rank_table[0]));writer.writeheader();writer.writerows(rank_table)
    # Weight-six row matrix: prove the rank is exactly seven directly as well.
    import sympy as sp
    words=list(admissible_words(6,3));rows=[]
    for word in words:
        factors=lyndon_factorization(word)
        if len(factors)>1:
            p=shuffle_many(factors);rows.append([p.get(v,0) for v in words])
    M=sp.Matrix(rows);assert M.shape==(7,10) and M.rank()==7
    counts['weight6_matrix_rank']=7
    counts['weight6_matrix_columns']=10
    # Print exact proof-backed identities using the elementary Gaussian atoms.
    p,l,G,z3,la3,la4=sp.symbols('p l G z3 la3 la4',real=True)
    L=-l/2+sp.I*p/4
    atoms={1:l/2+sp.I*p/4,
        2:5*p*p/96-l*l/8+sp.I*(G-p*l/8),
        3:35*z3/64-5*p*p*l/192+l**3/48+sp.I*la3,
        4:sp.Symbol('mu4',real=True)+sp.I*la4}
    def evalred(a,b):
        total=0
        for (j,S,T),c in one_zero_formula(a,b).items():
            term=sp.Rational(c.numerator,c.denominator)*L**j
            if S:term*=atoms[S[0]]
            if T:term*={2:p*p/6,3:z3,4:p**4/90}[T[0]]
            total+=term
        return sp.expand(sp.im(total))
    target=[la4+la3*l/2-G*(p*p-4*l*l)/32-p*(8*l**3+105*z3)/768,
        -3*la4-la3*l+G*(p*p-4*l*l)/32-3*p**3*l/256+p*(2*l**3+67*z3)/128,
        3*la4+la3*l/2+5*p**3*l/192-163*p*z3/256]
    for (a,b),expected in zip([(0,2),(1,1),(2,0)],target):
        assert sp.expand(evalred(a,b)-expected)==0
        counts['printed_gaussian_triples_symbolic_checks']+=1
    report=dict(status='PASS',arithmetic='exact rational; symbolic Gaussian specialization',
                scope='Finite checks supplement the all-weight proofs; no numerical independence inference.',
                checks=dict(counts))
    (ROOT/'certificates'/'exact_report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()

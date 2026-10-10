#!/usr/bin/env python3
"""Generate the declared weight-five level-four double-shuffle presentation.

This proves only a row-space obstruction in the stated finite presentation.
It does NOT disprove the numerical S4 identity or prove period independence.
Symbolic arithmetic uses SymPy; replay_certificate.py needs only Python.
"""
from __future__ import annotations
import json
from pathlib import Path
from math import comb
import sympy as S

pi, L, G, Z3, B4, Z5 = S.symbols('pi L G Z3 B4 Z5', real=True)
I = S.I
single = {
 1: [0, -L/2+I*pi/4, -L, -L/2-I*pi/4],
 2: [pi**2/6, -pi**2/48+I*G, -pi**2/12, -pi**2/48-I*G],
 3: [Z3, -3*Z3/32+I*pi**3/32, -3*Z3/4, -3*Z3/32-I*pi**3/32],
 4: [pi**4/90, -7*pi**4/11520+I*B4, -7*pi**4/720, -7*pi**4/11520-I*B4],
 5: [Z5, -15*Z5/512+I*5*pi**5/1536, -15*Z5/16,
     -15*Z5/512-I*5*pi**5/1536]
}
pairs = [(0,1), (1,0), (1,1), (1,2), (1,3), (2,1)]
variables = [(a,r,t) for a in range(1,5) for r,t in pairs]
atoms = [pi**5, G*Z3, B4*L]


def add_double(row, a, r, t, coefficient):
    r, t = r % 4, t % 4
    if (r,t) not in pairs:
        if ((-r)%4,(-t)%4) not in pairs:
            return  # Both colors are real: the imaginary coordinate is zero.
        r,t,coefficient = (-r)%4,(-t)%4,-coefficient
    row[variables.index((a,r,t))] += S.Rational(coefficient)


def add_product(row, expression, coefficient):
    v = S.expand(S.im(expression))
    recovered = 0
    for j, atom in enumerate(atoms):
        c = v.coeff(atom)
        row[len(variables)+j] += coefficient*c
        recovered += c*atom
    assert S.expand(v-recovered) == 0


def build_rows(regularized=True):
    rows, labels = [], []
    for p in range(1,5):
        q = 5-p
        for r in range(4):
            for t in range(4):
                divergent = (p == 1 and r == 0) or (q == 1 and t == 0)
                if divergent and not regularized:
                    continue
                product = single[p][r]*single[q][t]
                row = [S.Rational(0)]*27
                add_double(row,p,r,t,1)
                add_double(row,q,t,r,1)
                add_product(row,single[5][(r+t)%4],1)
                add_product(row,product,-1)
                if any(row):
                    rows.append(row)
                    labels.append(dict(law='stuffle',p=p,q=q,r=r,t=t))
                row = [S.Rational(0)]*27
                for j in range(p):
                    add_double(row,q+j,t,r-t,comb(q-1+j,j))
                for j in range(q):
                    add_double(row,p+j,r,t-r,comb(p-1+j,j))
                add_product(row,product,-1)
                if any(row):
                    rows.append(row)
                    labels.append(dict(law='shuffle',p=p,q=q,r=r,t=t))
    return rows, labels


def main():
    rows, labels = build_rows(True)
    target = [S.Rational(0)]*27
    for a,r,t,c in [(4,1,0,96),(3,1,0,96),(2,1,0,288),(4,1,2,224)]:
        add_double(target,a,r,t,c)
    target[-3:] = [S.Integer(-1),S.Integer(27),S.Integer(448)]
    sparse_w = {(1,1,0):-2, (2,0,1):1, (2,1,0):3, (2,1,3):-1,
                (3,0,1):-3, (3,1,0):-1, (3,1,3):-1, (4,0,1):2}
    witness = [sparse_w.get(key,0) for key in variables] + [0,0,0]
    M, T, w = S.Matrix(rows), S.Matrix([target]), S.Matrix(witness)
    assert M*w == S.zeros(len(rows),1)
    assert (T*w)[0] == 768
    assert M.rank() == 20 and M.col_join(T).rank() == 21
    unreg,_ = build_rows(False)
    assert len(unreg) == 88 and S.Matrix(unreg).rank() == 19
    result = dict(
        meaning='Obstruction in this explicit linear presentation only; not a disproof of S4.',
        columns=[f'X_{a};{r},{t}' for a,r,t in variables]+['pi^5','G*zeta(3)','beta(4)*log(2)'],
        rows=[[str(x) for x in row] for row in rows], row_labels=labels,
        target=[str(x) for x in target], witness=witness,
        shape=[len(rows),27], rank=20, augmented_rank=21,
        target_dot_witness=768, unregularized_shape=[88,27], unregularized_rank=19)
    path = Path(__file__).resolve().parents[1]/'certificates'/'s4_rowspace_obstruction.json'
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['shape','rank','augmented_rank','target_dot_witness']},indent=2))

if __name__ == '__main__':
    main()

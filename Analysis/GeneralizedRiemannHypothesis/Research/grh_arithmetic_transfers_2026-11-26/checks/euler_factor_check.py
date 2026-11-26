#!/usr/bin/env python3
"""Exact finite checks accompanying the Euler-factor interface lemmas.

The universal rank-two theorem is proved algebraically in the report.
The finite check below illustrates that theorem; it is not the proof.
The rank-three counterexample is verified exactly over the integers.
No external modules are needed.
"""
from itertools import product
import json


def matmul(a, b):
    return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def mateq(a,b):
    return all(x==y for ar,br in zip(a,b) for x,y in zip(ar,br))


def det3(a):
    x,y,z = a
    return x[0]*(y[1]*z[2]-y[2]*z[1])-x[1]*(y[0]*z[2]-y[2]*z[0])+x[2]*(y[0]*z[1]-y[1]*z[0])


def main():
    matrices_checked = 0
    annihilator_tests = 0
    for a,b,c,d in product(range(-2,3),repeat=4):
        determinant = a*d-b*c
        if determinant == 0:
            continue
        matrices_checked += 1
        matrix=[[a,b],[c,d]]
        square=matmul(matrix,matrix)
        for t in range(-8,9):
            annihilator_tests += 1
            is_zero = all(square[i][j]-t*matrix[i][j]+determinant*int(i==j)==0
                          for i,j in product(range(2),repeat=2))
            assert is_zero == (t==a+d)
    a=identity(3)
    b=[[0,0,1],[1,0,0],[0,1,0]]
    for matrix in (a,b):
        assert mateq(matmul(matmul(matrix,matrix),matrix),identity(3))
        assert det3(matrix)==1
        assert mateq(matmul([list(c) for c in zip(*matrix)],matrix),identity(3))
    assert sum(a[i][i] for i in range(3))==3
    assert sum(b[i][i] for i in range(3))==0
    print(json.dumps({
        "rank_two_integer_matrices_checked":matrices_checked,
        "annihilator_tests":annihilator_tests,
        "rank_three_counterexample":{
            "A":a,"B":b,"determinants":[1,1],"traces":[3,0],
            "common_squarefree_annihilator":"T^3 - 1",
            "characteristic_polynomials":["(T-1)^3","T^3-1"],
            "both_orthogonal":True
        },
        "interpretation":"Exact checks passed; general rank-two claim has a separate algebraic proof."
    },indent=2))


if __name__ == "__main__":
    main()

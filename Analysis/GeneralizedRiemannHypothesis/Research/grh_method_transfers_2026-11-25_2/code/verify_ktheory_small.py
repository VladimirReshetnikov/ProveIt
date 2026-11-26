#!/usr/bin/env python3
"""Independent exact reconstruction of two small compact Hecke operators.

Python standard library only. Reconstructs operators from 18 explicit unitary
matrices, using fresh evaluation points, and checks the published low-weight
values. This validates finite arithmetic, not the Selmer-to-K-theory bridge.

The mathematical setup and expected numbers are from Pintar's v1.0 supplement:
https://github.com/leopintar05/hecke-k-theory-104/tree/5c876949ccba300dbf580f7b3bbfd0e511856faf
No stored operator matrix is used as input to the reconstruction.
"""

from fractions import Fraction as F
from itertools import combinations, permutations
import argparse
import json
from math import prod, isqrt
from pathlib import Path


def add(a, b):
    return (a[0]+b[0], a[1]+b[1])


def neg(a):
    return (-a[0], -a[1])


def mul(a, b):
    return (a[0]*b[0]-3*a[1]*b[1], a[0]*b[1]+a[1]*b[0])


def conj(a):
    return (a[0], -a[1])


def scale(a, c):
    return (a[0]*c, a[1]*c)


ZERO, ONE = (F(0),F(0)), (F(1),F(0))


def total(values):
    answer = ZERO
    for value in values:
        answer = add(answer, value)
    return answer


def power(x, n):
    answer = ONE
    for _ in range(n):
        answer = mul(answer, x)
    return answer


def adjoint(matrix):
    return [[conj(matrix[j][i]) for j in range(3)] for i in range(3)]


def matmul(a, b):
    return [[total(mul(a[i][k], b[k][j]) for k in range(3))
             for j in range(3)] for i in range(3)]


IDENTITY = [[ONE if i==j else ZERO for j in range(3)] for i in range(3)]


def neighbors():
    zeta = (F(1,2),F(1,2))
    roots = [power(zeta, k) for k in range(6)]
    assert len(set(roots)) == 6 and power(zeta,6) == ONE
    answer = []
    for i,j in combinations(range(3), 2):
        for root in roots:
            b = mul((F(0),F(1)),root)
            g = [row[:] for row in IDENTITY]
            g[i][i] = g[j][j] = (F(1,2),F(0))
            g[i][j], g[j][i] = scale(b,F(1,2)), scale(neg(conj(b)),F(1,2))
            assert matmul(adjoint(g),g) == IDENTITY
            answer.append(g)
    # The integral basis at 2 is 1,(1+sqrt(-3))/2.
    integral_at_two = lambda a: (a[0]-a[1]).denominator % 2 and (2*a[1]).denominator % 2
    for g,h in combinations(answer,2):
        ratio=matmul(adjoint(g),h)
        assert any(not integral_at_two(a) for row in ratio for a in row)
    return answer


def apply(matrix, vector):
    return [total(mul(a,b) for a,b in zip(row,vector)) for row in matrix]


def invariant_values(x,y,e):
    z=[mul(a,b) for a,b in zip(x,y)]
    assert total(z)==ZERO
    s2=total(mul(z[i],z[j]) for i,j in combinations(range(3),2))
    s3=mul(mul(z[0],z[1]),z[2])
    if e==6:
        return [mul(s2,s3)]
    assert e==8
    left=total(mul(power(mul(x[i],y[j]),6),z[i]) for i,j in permutations(range(3),2))
    right=total(mul(power(mul(x[i],y[j]),6),z[j]) for i,j in permutations(range(3),2))
    return [mul(mul(s2,s2),s3),left,right]


def solve(a, b):
    n=len(a)
    augmented=[list(map(F,row))+[F(value)] for row,value in zip(a,b)]
    for j in range(n):
        pivot=next((i for i in range(j,n) if augmented[i][j]),None)
        if pivot is None:
            raise ValueError("singular evaluation matrix")
        augmented[j],augmented[pivot]=augmented[pivot],augmented[j]
        divisor=augmented[j][j]
        augmented[j]=[v/divisor for v in augmented[j]]
        for i in range(n):
            if i!=j:
                factor=augmented[i][j]
                augmented[i]=[x-factor*y for x,y in zip(augmented[i],augmented[j])]
    return [row[-1] for row in augmented]


def determinant(a):
    n=len(a)
    return sum((-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))
               *prod(a[i][p[i]] for i in range(n)) for p in permutations(range(n)))


def run():
    matrices=neighbors()
    points=[((1,2,3),(7,1,-3)),((2,3,5),(4,4,-4)),
            ((3,4,2),(2,1,-5)),((2,5,3),(1,-1,1)),
            ((1,3,2),(4,-2,1)),((5,1,2),(1,1,-3))]
    output={"status":"Finite exact arithmetic only; K-group bridge not verified",
            "cosets":len(matrices),"cases":[]}
    for e,n in ((6,1),(8,3)):
        E,H=[],[]
        for x0,y0 in points:
            x,y=[(F(a),F(0)) for a in x0],[(F(a),F(0)) for a in y0]
            values=invariant_values(x,y,e)
            transformed=[ZERO]*n
            for g in matrices:
                gy=[[conj(a) for a in row] for row in g]
                new=invariant_values(apply(g,x),apply(gy,y),e)
                transformed=[add(a,b) for a,b in zip(transformed,new)]
            assert all(a[1]==0 for a in values+transformed)
            E.append([a[0] for a in values]); H.append([a[0] for a in transformed])
        indices=next(I for I in combinations(range(len(E)),n)
                     if determinant([E[i] for i in I]))
        columns=[solve([E[i] for i in indices],[H[i][j] for i in indices]) for j in range(n)]
        T=[list(row) for row in zip(*columns)]
        assert all(sum(row[k]*T[k][j] for k in range(n))==target[j]
                   for row,target in zip(E,H) for j in range(n))
        shift=4**(2*e)+4**e+1
        difference=[[4**(e-1)*(T[i][j]+3*(i==j))-shift*(i==j)
                     for j in range(n)] for i in range(n)]
        value=determinant(difference)
        assert value.denominator==1
        case={"e":e,"K_degree":2*e,"dimension":n,
              "operator":[[str(v) for v in row] for row in T],
              "scaled_trace_difference_determinant":str(value.numerator),
              "evaluation_points_checked":len(points)}
        if e==6:
            assert T==[[F(99,128)]]
            assert value==-3**5*13*47*113
            case["determinant_prime_factors"]={3:5,13:1,47:1,113:1}
        else:
            integer_matrix=[[int(2048*v) for v in row] for row in T]
            assert all(F(v)*2048==w for row,ints in zip(T,integer_matrix) for v,w in zip(row,ints))
            assert integer_matrix==[[10215,-81081,-81081],[-81,-2421,11907],[-81,11907,-2421]]
            factors={3:13,5:2,7:1,11:2,23:1,401:1,809:1,1753:1,13109:1,13687:1}
            assert all(all(p%d for d in range(2,isqrt(p)+1)) for p in factors)
            assert value==-prod(p**a for p,a in factors.items())
            case["operator_times_2048"]=integer_matrix
            case["determinant_prime_factors"]=factors
        output["cases"].append(case)
    return output


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    args=parser.parse_args()
    result=run()
    text=json.dumps(result,indent=2)
    if args.output:
        args.output.write_text(text+"\n")
    print(text)
    print("PASS: two operators reconstructed exactly from explicit neighbors.")

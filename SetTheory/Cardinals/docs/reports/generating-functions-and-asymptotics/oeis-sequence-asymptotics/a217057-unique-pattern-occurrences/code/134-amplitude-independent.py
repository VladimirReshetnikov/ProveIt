"""Independent reconstruction: corner recursion and explicit cell columns.

No imports from certificate.py. No hook-length formula or interlacing-strip
enumeration. The finite certificate uses a directly summed (i,j) kernel.
"""
from fractions import Fraction
from functools import lru_cache
from math import comb


def check(condition, message):
    if not condition:
        raise ValueError(message)


@lru_cache(maxsize=None)
def recursive_dimension(shape):
    if shape == (0,0,0):
        return 1
    result = 0
    for row in range(3):
        next_length = shape[row+1] if row < 2 else 0
        if shape[row] > next_length:
            child = list(shape)
            child[row] -= 1
            result += recursive_dimension(tuple(child))
    check(result > 0, "invalid recursive tableau shape")
    return result


def young_layers(max_size):
    layers = [{(0,0,0)}]
    for n in range(1, max_size+1):
        next_layer = set()
        for shape in layers[-1]:
            for row in range(3):
                if row == 0 or shape[row] < shape[row-1]:
                    child = list(shape)
                    child[row] += 1
                    next_layer.add(tuple(child))
        layers.append(next_layer)
    return [{shape: recursive_dimension(shape) for shape in sorted(layer)}
            for layer in layers]


def is_horizontal(outer, inner):
    if any(inner[r] > outer[r] for r in range(3)):
        return False
    # List actual removed cells by column and reject a repeated column.
    columns = []
    for row in range(3):
        columns.extend(range(inner[row]+1, outer[row]+1))
    return len(columns) == len(set(columns))


def boundary_layers(max_size):
    dimensions = young_layers(max_size)
    matrices = []
    avoidance = [sum(d*d for d in layer.values()) for layer in dimensions]
    for n in range(max_size+1):
        matrix = [[0]*(n+1) for _ in range(n+1)]
        for outer, dim in dimensions[n].items():
            V = [0]*(n+1)
            for m in range(n+1):
                for inner, d in dimensions[m].items():
                    if is_horizontal(outer, inner):
                        V[n-m] += d
            check(V[0] == dim, "independent empty strip")
            check(all(0 <= x <= dim for x in V), "independent strip bound")
            for p in range(n+1):
                for q in range(n+1):
                    matrix[p][q] += V[p]*V[q]
        for p in range(n+1):
            check(matrix[p][p] <= comb(p+2,2)**2*avoidance[n-p],
                  "independent Cauchy/Pieri bound")
        matrices.append(matrix)
    return matrices, dimensions


def half_layers(matrices, T):
    result = []
    for t in range(T+1):
        layer = {}
        for i in range(t+2):
            for j in range(t+2):
                value = matrices[t+2][i+1][j+1]-matrices[t+1][i][j]
                check(value >= 0, "independent half positivity")
                check(i+j <= t or value == 0, "independent half support")
                if i+j <= t:
                    layer[i,j] = value
        result.append(layer)
    return result


def direct_kernel_certificate(layers, I):
    """Sum the finite i,j kernel before coupling to each H layer."""
    ds = [Fraction(comb(i+2,2), 3**i) for i in range(I+2)]
    C = [[81*ds[i+1]*ds[j+1]-9*ds[i]*ds[j]
          for j in range(I+1)] for i in range(I+1)]
    check(all(value > 0 for row in C for value in row), "kernel positivity")
    T = len(layers)-1
    binomials = [[comb(i+k,i) for i in range(I+1)] for k in range(T+1)]
    kernels = {}
    for k in range(T+1):
        for l in range(T+1-k):
            kernels[k,l] = sum((C[i][j]*binomials[k][i]*binomials[l][j]
                                for i in range(I+1) for j in range(I+1)), Fraction())
    result = Fraction()
    partials = []
    for t, layer in enumerate(layers):
        result += 2*sum((Fraction(h, 9**(t+4))*kernels[k,l]
                         for (k,l), h in layer.items()), Fraction())
        partials.append(result)
    return result, partials


def generating_function_boundary(k):
    """Coefficient extraction, independent of the displayed polynomials."""
    def coefficient(n):
        return Fraction(comb(n+2,2), 8)*Fraction(3,2)**n if n >= 0 else Fraction()
    D = 27*(coefficient(k)-2*coefficient(k-1)+coefficient(k-2))
    E = 27*(coefficient(k)-3*coefficient(k-1)+3*coefficient(k-2)-coefficient(k-3))
    if k == 0:
        E -= 1
    return D, E

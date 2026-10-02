"""Exact positive-stochastic lifts and natural quartic witnesses.

Python >=3.10, standard library only. Matrices act on column distributions.
Words are listed in chronological order: [i,j] means S_j S_i.
No finite test in this module is a decision procedure for unbounded mortality.
"""
from __future__ import annotations
from fractions import Fraction
from typing import Any, Sequence

Matrix = list[list[int]]


def identity(n: int) -> Matrix:
    return [[int(i == j) for j in range(n)] for i in range(n)]


def matmul(a, b):
    if not a or not b or len(a[0]) != len(b):
        raise ValueError("Incompatible matrix dimensions")
    return [[sum(a[i][s] * b[s][j] for s in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]


def kron(a, b):
    return [[x * y for x in ar for y in br] for ar in a for br in b]


def rank(a) -> int:
    """Gaussian rank over Q, without tolerance or floating-point conversion."""
    z = [[Fraction(x) for x in row] for row in a]
    m, n, r = len(z), len(z[0]), 0
    for j in range(n):
        p = next((i for i in range(r, m) if z[i][j]), None)
        if p is None:
            continue
        z[r], z[p] = z[p], z[r]
        lead = z[r][j]
        z[r] = [x / lead for x in z[r]]
        for i in range(r + 1, m):
            c = z[i][j]
            if c:
                z[i] = [x - c * y for x, y in zip(z[i], z[r])]
        r += 1
        if r == m:
            break
    return r


def integer_matrix(a: Any, n: int | None = None) -> Matrix:
    if not isinstance(a, (list, tuple)) or not a:
        raise ValueError("A matrix must be a nonempty array")
    n = len(a) if n is None else n
    if len(a) != n or any(not isinstance(row, (list, tuple)) or len(row) != n
                          for row in a):
        raise ValueError("Expected a square matrix of the specified size")
    if any(type(x) is not int for row in a for x in row):
        raise TypeError("Matrix entries must be exact integers (not bool/float)")
    return [list(row) for row in a]


def coordinates(h: int):
    n = h + 1
    e = identity(h) + [[-1] * h]
    f0 = [[n * int(i == j) - 1 for j in range(n)] for i in range(h)]
    return e, f0


def affine_lift(pairs: Sequence[tuple[Matrix, list[int]]],
                eta: Fraction = Fraction(1, 2)) -> dict:
    """Lift integer affine data to positive column-stochastic numerators."""
    if not isinstance(eta, Fraction) or not 0 < eta < 1:
        raise ValueError("eta must be an exact Fraction strictly between 0 and 1")
    if not pairs:
        raise ValueError("At least one affine map is required")
    h = len(pairs[0][0])
    n = h + 1
    e, f0 = coordinates(h)
    clean, deltas = [], []
    for c, b in pairs:
        c = integer_matrix(c, h)
        if len(b) != h or any(type(x) is not int for x in b):
            raise ValueError("Translation must be an integer vector")
        ecf = matmul(matmul(e, c), f0)
        eb = [sum(e[i][j] * b[j] for j in range(h)) for i in range(n)]
        delta = [[ecf[i][j] + n * eb[i] for j in range(n)] for i in range(n)]
        clean.append((c, list(b)))
        deltas.append(delta)
    maximum = max(abs(x) for a in deltas for row in a for x in row)
    ceiling = (maximum * eta.denominator + eta.numerator - 1) // eta.numerator
    scale = max(2, 1 + ceiling)
    nums = [[[scale + x for x in row] for row in a] for a in deltas]
    return {"n": n, "k": len(pairs), "K": scale, "D": n * scale,
            "eta": [eta.numerator, eta.denominator], "matrices": nums,
            "linear_parts": [p[0] for p in clean],
            "translations": [p[1] for p in clean]}


def compile_mortality(source: Sequence[Matrix], *, line_free: bool = True,
                      tensor_degree: int = 2,
                      eta: Fraction = Fraction(1, 2)) -> dict:
    """Compile a mortality instance, optionally excluding small invariant spaces.

    tensor_degree=2 uses the two unipotent guards of the main theorem.
    Larger degrees use the cyclic/diagonal guards of its extension.
    """
    if not source:
        raise ValueError("Source alphabet must not be empty")
    d = len(source[0])
    source = [integer_matrix(a, d) for a in source]
    if not line_free:
        pairs = [(a, [0] * d) for a in source]
        r = 1
    else:
        if type(tensor_degree) is not int or tensor_degree < 2:
            raise ValueError("Tensor degree must be an integer at least two")
        r = tensor_degree
        h = r * d
        pairs = [(kron(a, identity(r)), [0] * h) for a in source]
        if r == 2:
            p, q = [[1, 1], [0, 1]], [[1, 0], [1, 1]]
        else:
            p = [[int(i == (j + 1) % r) for j in range(r)] for i in range(r)]
            q = [[(i + 1) * int(i == j) for j in range(r)] for i in range(r)]
        pairs += [(kron(identity(d), p), [0] * h),
                  (kron(identity(d), q), [1] + [0] * (h - 1))]
    out = affine_lift(pairs, eta)
    out.update({"source": source, "source_count": len(source),
                "source_dimension": d, "tensor_degree": r,
                "line_free": line_free})
    return out


def product(matrices: Sequence[Matrix], word: Sequence[int]) -> Matrix:
    if not matrices:
        raise ValueError("Empty alphabet")
    ans = identity(len(matrices[0]))
    for i in word:
        if type(i) is not int or not 0 <= i < len(matrices):
            raise ValueError("Word letter out of range")
        ans = matmul(matrices[i], ans)
    return ans


def is_erasing(a: Matrix) -> bool:
    """Correct for positive-column-sum, column-stochastic numerators."""
    return all(row[j] == row[0] for row in a for j in range(1, len(row)))


def certificate(instance: dict, word: Sequence[int], target: str = "rank_one") -> dict:
    if not word or target not in ("rank_one", "uniform"):
        raise ValueError("Require a nonempty word and a supported target")
    n, k = instance["n"], instance["k"]
    x = identity(n)
    prefixes, selectors = [], []
    for i in word:
        if type(i) is not int or not 0 <= i < k:
            raise ValueError("Invalid letter")
        selectors.append([int(j == i) for j in range(k)])
        x = matmul(instance["matrices"][i], x)
        prefixes.append(x)
    return {"format": "exact-erasure-natural-quartic-v1", "n": n, "k": k,
            "D": instance["D"], "matrices": instance["matrices"],
            "T": len(word), "word": list(word), "target": target,
            "selectors": selectors, "prefixes": prefixes}


def perturb_numerators(instance: dict, q: int) -> dict:
    """S -> (1-1/q) S + (1/q) I, represented with common denominator qD."""
    if type(q) is not int or q < 2:
        raise ValueError("q must be an integer at least two")
    n, d = instance["n"], instance["D"]
    out = dict(instance)
    out["matrices"] = [[[(q - 1) * a[i][j] + d * int(i == j)
                          for j in range(n)] for i in range(n)]
                       for a in instance["matrices"]]
    out["D"] = q * d
    out["perturbation"] = [1, q]
    # Original affine coordinates/scale no longer describe these numerators.
    for key in ("K", "linear_parts", "translations", "eta"):
        out.pop(key, None)
    return out


def pcp_mortality(tiles: Sequence[tuple[str, str]]) -> list[Matrix]:
    """Explicit binary PCP -> 4x4 integer mortality (one idempotent connector).

    Symbols a,b are digits 1,2 in base 3. Empty component words are permitted.
    A PCP match [i1,...,it] gives the chronological zero word [q,i1,...,it,q],
    where q=len(tiles). The connector is idempotent, not square-zero.
    """
    if not tiles:
        raise ValueError("At least one PCP tile is required")
    def enc(s):
        if type(s) is not str or any(c not in "ab" for c in s):
            raise ValueError("PCP words must use only a,b")
        value = 0
        for c in s:
            value = 3 * value + (1 if c == "a" else 2)
        return value
    out = []
    for u, v in tiles:
        out.append([[3 ** len(u), 0, enc(u), 0],
                    [0, 3 ** len(v), enc(v), 0],
                    [0, 0, 1, 0], [0, 0, 0, 0]])
    c, ell = [0, 0, 1, 1], [1, -1, 0, 1]
    out.append([[x * y for y in ell] for x in c])
    return out


def information_certificate(instance: dict, word: Sequence[int]) -> dict:
    """Mass-compressed quartic: shifted signed restrictions to the zero-mass space."""
    if not word:
        raise ValueError("Require a nonempty word")
    n, k, D = instance["n"], instance["k"], instance["D"]
    h = n - 1
    if h < 1:
        raise ValueError("The information certificate requires n>=2")
    cs = [[[b[a][c] - b[a][h] for c in range(h)] for a in range(h)]
          for b in instance["matrices"]]
    y, power = identity(h), 1
    shifted, selectors = [], []
    for i in word:
        if type(i) is not int or not 0 <= i < k:
            raise ValueError("Invalid letter")
        selectors.append([int(j == i) for j in range(k)])
        y = matmul(cs[i], y)
        power *= D
        shifted.append([[v + power for v in row] for row in y])
    return {"format": "exact-erasure-information-quartic-v1", "n": n, "k": k,
            "D": D, "matrices": instance["matrices"], "T": len(word),
            "word": list(word), "selectors": selectors,
            "information_prefixes": shifted}

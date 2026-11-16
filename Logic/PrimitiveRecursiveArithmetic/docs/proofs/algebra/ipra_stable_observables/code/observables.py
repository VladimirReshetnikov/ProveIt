"""Finite rational certificates for intrinsic matrix observables.

The reference algorithms illustrate the report's constructions.  Their
exact checks do not constitute a completed Lean or iPRA formalization.
All searches have finite bounds.  Schur elimination decreases dimension;
the square-root scan uses a fixed binary-search fuel.
"""

from fractions import Fraction as F

from spectral import (matrix, identity, transpose, matmul, matsub, diagonal,
                      frob_sq, ceil_fraction, jacobi_grid, verify_certificate)


def quadratic_form(a, x):
    return sum((x[i] * a[i][j] * x[j]
                for i in range(len(a)) for j in range(len(a))), F(0))


def _unpermute_vector(x, order):
    answer = [F(0) for _ in order]
    for i, old_i in enumerate(order):
        answer[old_i] = x[i]
    return answer


def _psd_eliminate(a):
    """Return a PSD factor or negative vector; at most n Schur steps."""
    n = len(a)
    for i in range(n):
        if a[i][i] < 0:
            x = [F(j == i) for j in range(n)]
            return {"kind": "negative", "negative_vector": x,
                    "negative_value": a[i][i], "elimination_depth": 0}

    positive = [i for i in range(n) if a[i][i] > 0]
    if not positive:
        for i in range(n):
            for j in range(i + 1, n):
                if a[i][j] != 0:
                    x = [F(0) for _ in range(n)]
                    x[i] = F(1)
                    x[j] = F(-1 if a[i][j] > 0 else 1)
                    return {"kind": "negative", "negative_vector": x,
                            "negative_value": -2 * abs(a[i][j]),
                            "elimination_depth": 0}
        return {"kind": "psd", "L": identity(n),
                "d": [F(0) for _ in range(n)], "elimination_depth": 0}

    pivot = positive[0]
    order = [pivot] + [i for i in range(n) if i != pivot]
    permuted = [[a[i][j] for j in order] for i in order]
    p = permuted[0][0]
    v = [permuted[i][0] for i in range(1, n)]
    schur = [[permuted[i + 1][j + 1] - v[i] * v[j] / p
              for j in range(n - 1)] for i in range(n - 1)]
    child = _psd_eliminate(schur)
    if child["kind"] == "negative":
        y = child["negative_vector"]
        lifted = [-sum((v[i] * y[i] for i in range(n - 1)), F(0)) / p] + y
        x = _unpermute_vector(lifted, order)
        return {"kind": "negative", "negative_vector": x,
                "negative_value": quadratic_form(a, x),
                "elimination_depth": child["elimination_depth"] + 1}

    lower = [[F(0) for _ in range(n)] for _ in range(n)]
    lower[0][0] = F(1)
    for i in range(1, n):
        lower[i][0] = v[i - 1] / p
        for j in range(1, n):
            lower[i][j] = child["L"][i - 1][j - 1]
    factor = [[F(0) for _ in range(n)] for _ in range(n)]
    for i, old_i in enumerate(order):
        factor[old_i] = lower[i]
    return {"kind": "psd", "L": factor, "d": [p] + child["d"],
            "elimination_depth": child["elimination_depth"] + 1}


def psd_certificate(a):
    """Return A=L diag(d)L^T with d>=0, or x with x^T A x<0.

    L incorporates row permutations; it need not be triangular in the
    original coordinate order.  This is a permuted LDL certificate.
    """
    a = matrix(a)
    if a != transpose(a):
        raise ValueError("Input must be symmetric")
    return _psd_eliminate(a)


def verify_psd_result(a, result):
    """Check the finite output certificate without rerunning elimination."""
    a = matrix(a)
    n = len(a)
    if a != transpose(a) or not 0 <= result["elimination_depth"] <= n:
        return False
    if result["kind"] == "negative":
        x = result["negative_vector"]
        return (len(x) == n and quadratic_form(a, x) < 0
                and result["negative_value"] == quadratic_form(a, x))
    if result["kind"] != "psd":
        return False
    l, d = result["L"], result["d"]
    return (len(l) == n and all(len(row) == n for row in l)
            and len(d) == n and all(x >= 0 for x in d)
            and matmul(matmul(l, diagonal(d)), transpose(l)) == a)


def greatest_square_below(value, denominator, max_numerator):
    """Greatest j<=max_numerator with (j/denominator)^2<=value.

    The supplied upper bound must reach sqrt(value).  The binary search
    has fixed fuel determined by the bit length of the finite interval.
    """
    value = F(value)
    if value < 0 or denominator <= 0 or max_numerator < 0:
        raise ValueError("Invalid square search parameters")
    target = value * denominator ** 2
    if max_numerator ** 2 < target:
        raise ValueError("Square search upper bound is too small")
    low, high = 0, max_numerator + 1
    for _ in range((max_numerator + 1).bit_length() + 1):
        if high - low <= 1:
            break
        middle = (low + high) // 2
        if middle ** 2 <= target:
            low = middle
        else:
            high = middle
    if high - low != 1:
        raise AssertionError("Bounded square search exhausted its fuel")
    return low


def root_certificate(a, eta):
    """Produce rational PSD S with ||S^2-A||_F<=eta."""
    a, eta = matrix(a), F(eta)
    if eta <= 0:
        raise ValueError("eta must be positive")
    psd = psd_certificate(a)
    if psd["kind"] != "psd":
        raise ValueError("Input is not positive semidefinite")
    spectral = jacobi_grid(a, eta / 2)
    n = len(a)
    upper = 2 + ceil_fraction(frob_sq(a))
    denominator = max(1, ceil_fraction(F(2 * n * (2 * upper + 1), 1) / eta))
    integers = [greatest_square_below(d, denominator, upper * denominator)
                for d in spectral["d"]]
    roots = [F(j, denominator) for j in integers]
    q = spectral["Q"]
    s = matmul(matmul(q, diagonal(roots)), transpose(q))
    residual = matsub(matmul(s, s), a)
    result = {"S": s, "root_diagonal": roots, "root_numerators": integers,
              "denominator": denominator, "upper_bound": upper,
              "eta": eta, "residual_sq": frob_sq(residual),
              "spectral": spectral, "psd": psd}
    if result["residual_sq"] > eta ** 2:
        raise AssertionError("Root certificate failed the proved residual bound")
    return result


def verify_root_certificate(a, result):
    """Check root positivity, its finite construction data and residual."""
    a = matrix(a)
    n = len(a)
    spectral = result["spectral"]
    if (not verify_psd_result(a, result["psd"])
            or result["psd"]["kind"] != "psd"
            or not verify_certificate(a, spectral)):
        return False
    q, d = spectral["Q"], spectral["d"]
    roots, integers = result["root_diagonal"], result["root_numerators"]
    denominator, upper = result["denominator"], result["upper_bound"]
    eta, s = result["eta"], result["S"]
    if eta <= 0 or denominator <= 0 or len(roots) != n or len(integers) != n:
        return False
    if spectral["epsilon"] != eta / 2:
        return False
    if upper != 2 + ceil_fraction(frob_sq(a)):
        return False
    if denominator != max(1, ceil_fraction(F(2 * n * (2 * upper + 1), 1) / eta)):
        return False
    for i in range(n):
        j = integers[i]
        if not isinstance(j, int) or not 0 <= j <= upper * denominator:
            return False
        if roots[i] != F(j, denominator) or roots[i] < 0 or roots[i] ** 2 > d[i]:
            return False
        if j < upper * denominator and F(j + 1, denominator) ** 2 <= d[i]:
            return False
    expected = matmul(matmul(q, diagonal(roots)), transpose(q))
    residual_sq = frob_sq(matsub(matmul(s, s), a))
    return (s == expected and s == transpose(s)
            and result["residual_sq"] == residual_sq and residual_sq <= eta ** 2)


def projector_certificate(a, spectral, tau, gamma=None):
    """Threshold the diagonal of a supplied spectral certificate.

    No spectral-gap assertion is made when gamma is omitted.  If gamma
    is supplied, the finite diagonal-margin check must hold.
    """
    a, tau = matrix(a), F(tau)
    if not verify_certificate(a, spectral):
        raise ValueError("Invalid input spectral certificate")
    if gamma is not None:
        gamma = F(gamma)
        if gamma <= 0 or any(abs(d - tau) < gamma for d in spectral["d"]):
            raise ValueError("Requested diagonal margin is not certified")
    flags = [F(int(d < tau)) for d in spectral["d"]]
    q = spectral["Q"]
    p = matmul(matmul(q, diagonal(flags)), transpose(q))
    commutator = matsub(matmul(a, p), matmul(p, a))
    return {"P": p, "flags": flags, "rank": int(sum(flags, F(0))),
            "tau": tau, "gamma": gamma, "spectral": spectral,
            "commutator_sq": frob_sq(commutator)}


def verify_projector_certificate(a, result):
    """Check projection, rank, approximate commutation and margin."""
    a = matrix(a)
    spectral = result["spectral"]
    if not verify_certificate(a, spectral):
        return False
    q, d = spectral["Q"], spectral["d"]
    flags, p = result["flags"], result["P"]
    tau, gamma = result["tau"], result["gamma"]
    if flags != [F(int(x < tau)) for x in d]:
        return False
    if gamma is not None and (gamma <= 0 or any(abs(x - tau) < gamma for x in d)):
        return False
    commutator_sq = frob_sq(matsub(matmul(a, p), matmul(p, a)))
    return (p == matmul(matmul(q, diagonal(flags)), transpose(q))
            and p == transpose(p) and matmul(p, p) == p
            and result["rank"] == sum(flags, F(0))
            and sum((p[i][i] for i in range(len(p))), F(0)) == result["rank"]
            and result["commutator_sq"] == commutator_sq
            and commutator_sq <= spectral["epsilon"] ** 2)

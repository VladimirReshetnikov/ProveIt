"""Fresh stdlib exact algebra for corrected alternating Baxter involutions.

All series are coefficient lists truncated after the requested degree.
No source report implementation is imported or used.
"""
from fractions import Fraction as F
from math import comb


class VerificationError(ValueError):
    """A mathematical or evidence invariant failed."""


def require(condition, message):
    if not condition:
        raise VerificationError(message)


def recurrence(limit, *, corrected=True):
    if type(limit) is not int or limit < 0:
        raise ValueError("limit must be a nonnegative integer")
    even, odd = [1], [1]
    catalan = [comb(2*j, j)//(j+1) for j in range(limit + 1)]
    for m in range(1, limit + 1):
        odd.append(sum(even[i]*odd[m-1-i] for i in range(m)))
        factors = catalan if corrected else odd
        even.append(odd[m-1] + sum(factors[j]*even[m-2*j-2]
                                  for j in range(m//2)))
    return even, odd


def interleave(even, odd):
    require(len(even) == len(odd), "parity lengths differ")
    return [v for pair in zip(even, odd) for v in pair]


def add(a, b, n):
    return [(a[k] if k < len(a) else F(0)) +
            (b[k] if k < len(b) else F(0)) for k in range(n+1)]


def scale(a, c):
    return [c*v for v in a]


def multiply(a, b, n):
    result = [F(0)]*(n+1)
    for i, ai in enumerate(a[:n+1]):
        if ai:
            for j, bj in enumerate(b[:n+1-i]):
                if bj:
                    result[i+j] += ai*bj
    return result


def reciprocal(a, n):
    require(bool(a) and a[0] != 0, "series has no reciprocal")
    result = [F(1)/a[0]]
    for k in range(1, n+1):
        result.append(-sum(a[j]*result[k-j]
                           for j in range(1, min(k, len(a)-1)+1))/a[0])
    return result


def square_root_one(a, n):
    require(bool(a) and a[0] == 1, "square-root branch must start at one")
    result = [F(1)]
    for k in range(1, n+1):
        ak = a[k] if k < len(a) else F(0)
        result.append((ak - sum(result[j]*result[k-j]
                                for j in range(1, k)))/2)
    return result


def radical_coefficients(limit):
    """Expand radicals, never consulting the enumeration recurrence."""
    if type(limit) is not int or limit < 0:
        raise ValueError("limit must be a nonnegative integer")
    degree = limit + 2  # O's removable x^2 denominator loses two degrees.
    u = square_root_one([F(1), F(0), F(-4)], degree)
    M = scale(add([F(1)], u, degree), F(1, 2))
    D = multiply(M, [F(1), F(-2), F(-4)], degree)
    root_D = square_root_one(D, degree)
    numerator = add(add(M, [F(0), F(-1)], degree),
                    scale(root_D, -1), degree)
    require(numerator[:2] == [0, 0], "radical's origin is not removable")
    odd = scale(numerator[2:], F(1, 2))
    even = multiply(add([F(1)], [F(0)] + odd, limit),
                    reciprocal(M, limit), limit)
    require(all(v.denominator == 1 for v in even + odd),
            "radical coefficient is nonintegral")
    return [int(v) for v in even], [int(v) for v in odd]


def algebraic_residuals(even, odd):
    """Exact functional, discriminant and quartic identities, to finite order."""
    n = min(len(even), len(odd))-1
    E, O = list(map(F, even)), list(map(F, odd))
    C2 = [F(comb(k, k//2)//(k//2+1)) if k % 2 == 0 else F(0)
          for k in range(n+1)]
    M = add([F(1)], scale([F(0), F(0)] + C2, -1), n)
    zero = [F(0)]*(n+1)
    # O(1-xE)-1=0 and E(1-x^2 C(x^2))-1-xO=0.
    first = add(multiply(O, add([F(1)], scale([F(0)] + E, -1), n), n),
                [F(-1)], n)
    second = add(add(multiply(E, M, n), [F(-1)], n),
                 scale([F(0)] + O, -1), n)
    Mminusx = add(M, [F(0), F(-1)], n)
    D1 = add(multiply(Mminusx, Mminusx, n),
             scale([F(0), F(0)] + M, -4), n)
    D2 = multiply(M, [F(1), F(-2), F(-4)], n)
    H = add(O, [F(-1)], n)
    P0 = add(add([F(0), F(0)] + multiply(O, O, n),
                 scale(multiply([F(1), F(-1)], O, n), -1), n),
             [F(1)], n)
    quartic = add(add(multiply(P0, P0, n), multiply(H, P0, n), n),
                  [F(0), F(0)] + multiply(H, H, n), n)
    residuals = {"O_times_1_minus_xE_minus_1": first,
                 "E_times_M_minus_1_minus_xO": second,
                 "discriminant_factorization": add(D1, scale(D2, -1), n),
                 "quartic_relation": quartic}
    for name, values in residuals.items():
        require(values == zero, name + " failed")
    return {name: [int(v) for v in values] for name, values in residuals.items()}


# Laurent polynomials in beta,p,d1,d2,d3,d4; beta alone may have negative powers.
# This tiny exact ring permits an identity in symbols, not numeric spot checks.
class Laurent:
    variables = ("beta", "p", "d1", "d2", "d3", "d4")

    def __init__(self, terms=None):
        self.terms = {tuple(k): F(v) for k, v in (terms or {}).items() if v}

    @classmethod
    def constant(cls, v):
        return cls({(0, 0, 0, 0, 0, 0): F(v)})

    @classmethod
    def variable(cls, index, power=1):
        powers = [0]*6
        powers[index] = power
        return cls({tuple(powers): 1})

    def __add__(self, other):
        if not isinstance(other, Laurent):
            other = self.constant(other)
        terms = dict(self.terms)
        for monomial, value in other.terms.items():
            terms[monomial] = terms.get(monomial, F(0)) + value
        return Laurent(terms)

    __radd__ = __add__

    def __neg__(self):
        return Laurent({k: -v for k, v in self.terms.items()})

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        if not isinstance(other, Laurent):
            other = self.constant(other)
        terms = {}
        for ka, va in self.terms.items():
            for kb, vb in other.terms.items():
                key = tuple(x+y for x, y in zip(ka, kb))
                terms[key] = terms.get(key, F(0)) + va*vb
        return Laurent(terms)

    __rmul__ = __mul__

    def __eq__(self, other):
        if not isinstance(other, Laurent):
            other = self.constant(other)
        return self.terms == other.terms

    def __bool__(self):
        return bool(self.terms)

    def encoded(self):
        return [{"powers": list(k), "coefficient": str(v)}
                for k, v in sorted(self.terms.items())]


def inverse_residual(coefficients, degree=4):
    """Expand beta*u-p*log(1+eps*u)+sum d_j eps^j/(1+eps*u)^j."""
    beta, p, d1, d2, d3, d4 = [Laurent.variable(i) for i in range(6)]
    u = [Laurent()] + list(coefficients)
    u += [Laurent()] * max(0, degree+1-len(u))
    t = [Laurent()] + u
    # Generic finite binomial expansions; t has zero constant term.
    powers = [[Laurent.constant(1)] + [Laurent()]*degree]
    for k in range(1, degree+1):
        powers.append(multiply(powers[-1], t, degree))
    logarithm = [Laurent()]*(degree+1)
    for k in range(1, degree+1):
        logarithm = add(logarithm, scale(powers[k], F((-1)**(k+1), k)), degree)
    result = add(scale(u, beta), scale(logarithm, -p), degree)
    for j, dj in enumerate((d1, d2, d3, d4), 1):
        factor = [Laurent()]*(degree+1)
        for k in range(degree+1):
            factor = add(factor, scale(powers[k], (-1)**k*comb(j+k-1, k)), degree)
        result = add(result, [Laurent()]*j + scale(factor, dj), degree)
    return result


def inverse_identity_evidence():
    beta, p, d1, d2, d3, d4 = [Laurent.variable(i) for i in range(6)]
    inv_beta = Laurent.variable(0, -1)
    v1 = -d1*inv_beta
    v2 = (p*v1-d2)*inv_beta
    v3 = (p*v2+d1*v1-d3)*inv_beta
    v4 = (p*v3-F(1, 2)*p*v1*v1+d1*v2+2*d2*v1-d4)*inv_beta
    displayed = [v1, v2, v3, v4]
    # Derive each unknown afresh by cancelling its first affected coefficient.
    derived = []
    for k in range(1, 5):
        residual = inverse_residual(derived, degree=k)
        derived.append(-residual[k]*inv_beta)
    require(derived == displayed, "inverse coefficients disagree with reversion")
    residual = inverse_residual(displayed)
    require(all(not c for c in residual), "formal inverse residual is nonzero")
    for k in range(4):
        altered = displayed.copy()
        altered[k] = altered[k] + 1
        require(any(inverse_residual(altered)), "inverse coefficient mutation escaped")
    return {"ring_variables": list(Laurent.variables),
            "condition": "beta != 0; p arbitrary (the application uses p=3/2)",
            "coefficients_v1_v2_v3_v4": [v.encoded() for v in displayed],
            "residual_coefficients_epsilon_0_through_4": [c.encoded() for c in residual],
            "independent_coefficient_reversion_matches": True,
            "each_single_coefficient_plus_one_rejected": True,
            "scope": "Formal identity only; no finite inverse error constants or onset certified."}

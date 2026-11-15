"""Independent exact polynomial expansion with integer coefficients.

The small normalizer below does not import a CAS.  A zero residual is evidence
that the displayed fixed algebraic identity is correct; this is not a checked
object-language derivation or a proof of the normalizer's soundness in Lean.
"""

NAMES = ("x", "y", "z", "w", "a", "b", "c")
ZERO_MONOMIAL = (0,) * len(NAMES)


class Poly:
    def __init__(self, terms=None):
        self.terms = {m: c for m, c in (terms or {}).items() if c}

    @staticmethod
    def coerce(v):
        return v if isinstance(v, Poly) else Poly({ZERO_MONOMIAL: int(v)})

    def __add__(self, other):
        out = dict(self.terms)
        for m, c in self.coerce(other).terms.items():
            out[m] = out.get(m, 0) + c
        return Poly(out)

    __radd__ = __add__

    def __neg__(self):
        return Poly({m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) + -self

    def __mul__(self, other):
        out = {}
        for m, c in self.terms.items():
            for n, d in self.coerce(other).terms.items():
                mon = tuple(i+j for i, j in zip(m, n))
                out[mon] = out.get(mon, 0) + c*d
        return Poly(out)

    __rmul__ = __mul__

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        result = self.coerce(1)
        for _ in range(n):
            result *= self
        return result


def var(name):
    exponents = [0] * len(NAMES)
    exponents[NAMES.index(name)] = 1
    return Poly({tuple(exponents): 1})


def check_all():
    x, y, z, w, a, b, c = map(var, NAMES)
    U, V = x*x+y*y, z*z+w*w
    W, p, t = (x-z)**2+(y-w)**2, x*z+y*w, x*w-y*z
    nx, ny = U*w-V*y, V*x-U*z
    factor = (a+b+c)*(-a+b+c)*(a-b+c)*(a+b-c)
    identities = {
        "cosine_polynomial": (W, U+V-2*p),
        "gram": (U*V, p*p+t*t),
        "heron_coordinates": (
            2*(W*V+V*U+U*W)-W*W-V*V-U*U, 4*t*t),
        "heron_factorization": (
            factor, 2*(a*a*b*b+b*b*c*c+c*c*a*a)-a**4-b**4-c**4),
        "heron_factorization_gram": (factor, 4*b*b*c*c-(b*b+c*c-a*a)**2),
        "center_dot_u": (x*nx+y*ny, U*t),
        "center_dot_v": (z*nx+w*ny, V*t),
        "center_norm": (nx*nx+ny*ny, U*V*W),
        "center_equidistant_u": (
            (nx-2*t*x)**2+(ny-2*t*y)**2, nx*nx+ny*ny),
        "center_equidistant_v": (
            (nx-2*t*z)**2+(ny-2*t*w)**2, nx*nx+ny*ny),
        "det_at_B": ((-x)*(w-y)-(-y)*(z-x), -t),
        "det_at_C": ((-z)*(y-w)-(-w)*(x-z), t),
        "two_angle_real_numerator": (p*(U-p)-t*t, U*(p-V)),
        "two_angle_imag_numerator": (a*p+a*(U-p), a*U),
        "side_reconstruction": (
            4*b*b*c*c-(b*b+c*c-a*a)**2, factor),
    }
    results = []
    for name, (lhs, rhs) in identities.items():
        residual = lhs-rhs
        assert not residual.terms, (name, residual.terms)
        results.append({"identity": name, "zero_residual": True,
                        "expanded_terms_left": len(lhs.terms),
                        "expanded_terms_right": len(rhs.terms)})
    return results


if __name__ == "__main__":
    import json
    print(json.dumps(check_all(), indent=2))

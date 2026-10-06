#!/usr/bin/env python3
"""Report146 finite exact algebra checks; standard library only.

No finite check establishes the report's analytic estimates or certifies digits.
Input is a bounded, closed, semantically checked JSON fixture, not executable code.
"""
import argparse
from fractions import Fraction as Q
import hashlib
import json
import math
import os
from pathlib import Path
import re
import stat
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).absolute().parent
MAX_BYTES = 65536
MAX_DEPTH = 24
MAX_PUNCTUATION = 6000
SCHEMA = "report146-exact-v1"
SCOPE = "finite exact identities only; no analytic proof or new certified digits"
INPUT_LABELS = (
    "A1: normalized placement recurrence and all-index positivity",
    "A2: cleared second-logarithm rate and second-order constant identification",
    "A3: critical boundary condition for the exact inverse",
    "A4: uniform kernel remainders, signed convolution bounds, convergent moments",
    "A5: fixed-order forward remainder and positive-prefix argument for root inversion",
    "A6: real-axis bounds and evaluator termination for rate enclosures",
)
KERNEL_KEYS = ("r1", "r2", "r3", "p", "b2", "b3", "q", "f", "h3",
               "Umean", "S0", "UV", "c", "a2", "L2_constant", "L2_SA",
               "third_x_constant", "third_x_SA", "third_sqrt_constant",
               "third_sqrt_SA", "log_squared", "B3_normalization_shift")
SYMBOLS = ("b", "c", "k", "a", "d", "e", "lambda_inverse", "ell")


class CheckError(Exception):
    """Invalid input, false identity, or unsafe filesystem operation."""


def require(condition, message):
    if not condition:
        raise CheckError(message)


def obj(value, keys, where):
    require(type(value) is dict, where + ": object required")
    require(set(value) == set(keys), where + ": unknown or missing keys")


def integer(value, lower, upper, where):
    require(type(value) is int, where + ": integer required (not bool/float)")
    require(lower <= value <= upper, where + ": integer out of range")
    return value


def array(value, lower, upper, where):
    require(type(value) is list, where + ": array required")
    require(lower <= len(value) <= upper, where + ": array size out of range")
    return value


def rational(value, where):
    require(type(value) is str, where + ": canonical rational string required")
    require(len(value) <= 51 and re.fullmatch(r"-?(?:0|[1-9][0-9]{0,23})/[1-9][0-9]{0,23}", value) is not None,
            where + ": invalid or oversized rational")
    n, d = map(int, value.split("/"))
    require(value != "-0/1" and math.gcd(n, d) == 1, where + ": noncanonical rational")
    return Q(n, d)


def qstr(value):
    return str(value.numerator) + "/" + str(value.denominator)


def no_duplicates(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate JSON key: " + key)
        result[key] = value
    return result


def json_integer(value):
    require(len(value) <= 6, "JSON integer token too large")
    return int(value)


def forbidden_number(value):
    raise CheckError("JSON noninteger numbers forbidden: " + value)


def parse_json(raw):
    require(type(raw) is bytes and len(raw) <= MAX_BYTES, "fixture byte bound exceeded")
    try:
        text = raw.decode("utf-8")
        depth = punctuation = 0
        quoted = escaped = False
        for ch in text:
            if quoted:
                if escaped:
                    escaped = False
                elif ch == "\\":
                    escaped = True
                elif ch == '"':
                    quoted = False
            elif ch == '"':
                quoted = True
            elif ch in "[{":
                depth += 1
                punctuation += 1
                require(depth <= MAX_DEPTH, "JSON nesting bound exceeded")
            elif ch in "]}":
                depth -= 1
                require(depth >= 0, "unbalanced JSON")
            elif ch in ",:":
                punctuation += 1
            require(punctuation <= MAX_PUNCTUATION, "JSON structure bound exceeded")
        return json.loads(text, object_pairs_hook=no_duplicates, parse_int=json_integer,
                          parse_float=forbidden_number, parse_constant=forbidden_number)
    except (UnicodeError, ValueError, RecursionError) as exc:
        raise CheckError("invalid UTF-8 JSON: " + str(exc)) from exc


def interval(value, where):
    array(value, 2, 2, where)
    lo, hi = (rational(v, where) for v in value)
    require(lo <= hi, where + ": reversed interval")
    return lo, hi


def validate_fixture(d):
    obj(d, ("schema", "scope", "analytic_inputs", "log_models", "signed_taylor",
            "inverse", "kernel", "moments", "formal_inverse", "synthetic_intervals", "acceleration"), "fixture")
    require(type(d["schema"]) is str and d["schema"] == SCHEMA, "unsupported schema")
    require(type(d["scope"]) is str and d["scope"] == SCOPE, "invalid scope label")
    require(type(d["analytic_inputs"]) is list and tuple(d["analytic_inputs"]) == INPUT_LABELS,
            "analytic input labels must be exact and ordered")
    l = d["log_models"]
    obj(l, ("n_max", "q_max", "a_max", "anchors"), "log_models")
    integer(l["n_max"], 12, 48, "log_models.n_max")
    integer(l["q_max"], 2, 6, "log_models.q_max")
    integer(l["a_max"], 1, 5, "log_models.a_max")
    array(l["anchors"], 4, 24, "log_models.anchors")
    seen = set()
    for row in l["anchors"]:
        obj(row, ("a", "q", "n", "value"), "anchor")
        a = integer(row["a"], -1, l["a_max"], "anchor.a")
        q = integer(row["q"], 0, l["q_max"], "anchor.q")
        n = integer(row["n"], 0, l["n_max"], "anchor.n")
        require((a, q, n) not in seen, "duplicate anchor")
        seen.add((a, q, n))
        rational(row["value"], "anchor.value")
    t = d["signed_taylor"]
    obj(t, ("samples",), "signed_taylor")
    array(t["samples"], 3, 12, "signed_taylor.samples")
    for row in t["samples"]:
        obj(row, ("values", "n", "i", "order", "expected"), "Taylor sample")
        vals = array(row["values"], 6, 48, "Taylor.values")
        vals = [rational(v, "Taylor value") for v in vals]
        require(min(vals) < 0 < max(vals), "Taylor fixture must exercise signed values")
        n = integer(row["n"], 1, len(vals)-1, "Taylor.n")
        integer(row["i"], 0, n, "Taylor.i")
        integer(row["order"], 1, min(8, n+1), "Taylor.order")
        rational(row["expected"], "Taylor.expected")
    inv = d["inverse"]
    obj(inv, ("unit_max", "tail_end", "models"), "inverse")
    integer(inv["unit_max"], 4, 24, "inverse.unit_max")
    integer(inv["tail_end"], 12, 40, "inverse.tail_end")
    array(inv["models"], 6, 28, "inverse.models")
    seen = set()
    for row in inv["models"]:
        obj(row, ("a", "q", "critical_constant"), "inverse model")
        a = integer(row["a"], -1, 5, "inverse.a")
        q = integer(row["q"], 0, 6, "inverse.q")
        require((a, q) not in seen, "duplicate inverse model")
        seen.add((a, q))
        rational(row["critical_constant"], "inverse.critical_constant")
    obj(d["kernel"], KERNEL_KEYS, "kernel")
    for key in KERNEL_KEYS:
        rational(d["kernel"][key], "kernel." + key)
    m = d["moments"]
    obj(m, ("orders", "counts"), "moments")
    array(m["orders"], 4, 12, "moments.orders")
    array(m["counts"], len(m["orders"]), len(m["orders"]), "moments.counts")
    previous = 0
    for order, count in zip(m["orders"], m["counts"]):
        integer(order, 1, 12, "moment order")
        require(order > previous, "moment orders must be strictly increasing")
        integer(count, 1, 364, "moment count")
        previous = order
    f = d["formal_inverse"]
    obj(f, ("symbols", "R1", "R2", "R3"), "formal_inverse")
    require(type(f["symbols"]) is list and tuple(f["symbols"]) == SYMBOLS, "invalid symbol order")
    for name in ("R1", "R2", "R3"):
        array(f[name], 1, 16, name)
        previous = None
        for term in f[name]:
            obj(term, ("powers", "coefficient"), name + " term")
            array(term["powers"], 8, 8, "powers")
            key = tuple(integer(v, 0, 4, "power") for v in term["powers"])
            require(sum(key) <= 6, "monomial total-degree bound exceeded")
            require(previous is None or previous < key, "monomials must be unique and sorted")
            require(rational(term["coefficient"], "monomial coefficient") != 0, "omit zero monomials")
            previous = key
    array(d["synthetic_intervals"], 2, 8, "synthetic_intervals")
    for row in d["synthetic_intervals"]:
        obj(row, ("z", "a", "v", "C", "expected"), "interval example")
        require(rational(row["z"], "z") > 0, "z must be positive")
        for key in ("a", "v", "C"):
            require(interval(row[key], key)[0] > 0, key + " must be positive")
        require(interval(row["a"], "a")[1] < 1, "a must be below one")
        obj(row["expected"], ("A", "B", "P"), "expected intervals")
        for key in ("A", "B", "P"):
            interval(row["expected"][key], "expected." + key)
    ac = d["acceleration"]
    obj(ac, ("max_J", "weights_J3", "ratio"), "acceleration")
    integer(ac["max_J"], 3, 6, "acceleration.max_J")
    array(ac["weights_J3"], 5, 5, "weights_J3")
    for value in ac["weights_J3"]:
        rational(value, "accelerator weight")
    obj(ac["ratio"], ("first", "second", "third_log", "third_rational", "third_B2"), "ratio")
    for value in ac["ratio"].values():
        rational(value, "ratio coefficient")
    return d


# Exact univariate polynomials in increasing powers. Also used for v-polynomials.
def trim(a):
    a = tuple(Q(x) for x in a)
    while len(a) > 1 and a[-1] == 0:
        a = a[:-1]
    return a or (Q(0),)


def add(a, b):
    return trim((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
                for i in range(max(len(a), len(b))))


def scale(a, c):
    return trim(x*c for x in a)


def mul(a, b):
    out = [Q(0)]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return trim(out)


def integrate(a):
    return sum((c/Q(i+1) for i, c in enumerate(a)), Q(0))


def reflect(a):
    out = (Q(0),)
    for k, c in enumerate(a):
        out = add(out, tuple(c*((-1)**j)*math.comb(k, j) for j in range(k+1)))
    return out


def convolution(a, b, N):
    return [sum((a[i]*b[n-i] for i in range(n+1)), Q(0)) for n in range(N+1)]


def log_power_by_products(q, N):
    base = [Q(0)] + [Q(1, n) for n in range(1, N+1)]
    out = [Q(1)] + [Q(0)]*N
    for unused in range(q):
        out = convolution(out, base, N)
    return out


def log_power_by_symmetric(q, N):
    if q == 0:
        return [Q(1)] + [Q(0)]*N
    out = [Q(0)]
    e = [Q(1)] + [Q(0)]*(q-1)
    for n in range(1, N+1):
        out.append(Q(math.factorial(q), n)*e[q-1])
        for k in range(q-1, 0, -1):
            e[k] += e[k-1]/n
    return out


def upower(a, N):
    if a == -1:
        return [Q(1)]*(N+1)
    return [Q((-1)**n*math.comb(a, n)) if n <= a else Q(0) for n in range(N+1)]


def model(a, q, N):
    return convolution(upower(a, N), log_power_by_symmetric(q, N), N)


def inverse_model(a, q, N):
    out = [Q(0)]*(N+1)
    for j in range(q+1):
        c = -Q(math.factorial(q), math.factorial(q-j)*(a+3)**(j+1))
        v = model(a+1, q-j, N)
        out = [x+c*y for x, y in zip(out, v)]
    return out


def backward(values, n, k):
    return sum((Q((-1)**j*math.comb(k, j))*values[n-j] for j in range(k+1)), Q(0))


def kernel_values():
    order = 3
    r = [Q(0)]*(order+1)
    for k in range(1, order+1):
        m = k+1
        target = Q((-1)**(m+2), m+1) + Q((-1)**(m+1), 2*m)
        prior = sum((r[j]*(-(-1)**(m-j)*math.comb(m-1, m-j)) for j in range(1, k)), Q(0))
        r[k] = (target-prior)/k
    glog = [(Q(0),)]*(order+1)
    hlog = [Q(0)]*(order+1)
    for k in range(1, order+1):
        terms = [Q((-1)**(k+1), 2*k)-r[k]] + [Q(0)]*k + [Q((-1)**k, k+1)]
        glog[k] = trim(terms)
        hlog[k] = -Q((-1)**(k+1)*2**k, 2*k)+r[k]+Q((-1)**(k+1), k+1)
    G = [(Q(1),)] + [(Q(0),)]*order
    H = [Q(1)] + [Q(0)]*order
    for n in range(1, order+1):
        v = (Q(0),)
        for k in range(1, n+1):
            v = add(v, scale(mul(glog[k], G[n-k]), Q(k, n)))
            H[n] += Q(k, n)*hlog[k]*H[n-k]
        G[n] = v
    d = Q(-1, 4)
    U = add((d,), G[1])
    V_without_C = add(scale(G[1], d), G[2])
    p, b2, b3 = (integrate(G[i]) for i in (1, 2, 3))
    q, f, h3 = H[1:]
    Umean = integrate(U)
    S0 = integrate(mul(U, reflect(U)))
    UV = integrate(mul(U, reflect(V_without_C)))
    c = 2*S0/3
    A2 = (-2*UV, -c)  # polynomial in S_A
    L2 = add((-(p+2*q)*c+2*q*S0,), scale(A2, -2))
    third_x = add((c,), scale(L2, Q(1, 2)))
    third_sqrt = add(third_x, (c/2,))
    out = dict(zip(("r1", "r2", "r3"), r[1:]))
    out.update(p=p, b2=b2, b3=b3, q=q, f=f, h3=h3, Umean=Umean,
               S0=S0, UV=UV, c=c, a2=b2+p*d, L2_constant=L2[0], L2_SA=L2[1],
               third_x_constant=third_x[0], third_x_SA=third_x[1],
               third_sqrt_constant=third_sqrt[0], third_sqrt_SA=third_sqrt[1],
               log_squared=2*(-c/2)*Umean,
               B3_normalization_shift=Q(1, 16)-d/8)
    require(G[1] == (Q(5, 12), Q(0), Q(-1, 2)), "G1 polynomial mismatch")
    require(G[2] == (Q(-47, 288), Q(0), Q(-5, 24), Q(1, 3), Q(1, 8)), "G2 polynomial mismatch")
    require(integrate(reflect(U)) == Umean, "reflection integral identity")
    return out


# Sparse multivariate rational polynomials. Zero has an empty coefficient map.
class Polynomial:
    def __init__(self, terms=None):
        self.terms = {k: Q(v) for k, v in (terms or {}).items() if v}

    @staticmethod
    def constant(value):
        return Polynomial({(0,)*8: Q(value)})

    @staticmethod
    def coerce(value):
        return value if isinstance(value, Polynomial) else Polynomial.constant(value)

    def __add__(self, other):
        other = self.coerce(other)
        out = dict(self.terms)
        for key, value in other.terms.items():
            out[key] = out.get(key, Q(0)) + value
        return Polynomial(out)

    __radd__ = __add__

    def __neg__(self):
        return Polynomial({k: -v for k, v in self.terms.items()})

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) + -self

    def __mul__(self, other):
        other = self.coerce(other)
        out = {}
        for k, v in self.terms.items():
            for j, w in other.terms.items():
                key = tuple(x+y for x, y in zip(k, j))
                out[key] = out.get(key, Q(0)) + v*w
        return Polynomial(out)

    __rmul__ = __mul__

    def __eq__(self, other):
        return self.terms == self.coerce(other).terms

    def divide_lambda_inverse(self):
        out = {}
        for key, value in self.terms.items():
            require(key[6] >= 1, "formal inverse is not divisible by lambda_inverse")
            new = list(key)
            new[6] -= 1
            out[tuple(new)] = value
        return Polynomial(out)


def variable(index):
    key = [0]*8
    key[index] = 1
    return Polynomial({tuple(key): Q(1)})


def sconstant(value, N):
    return [Polynomial.coerce(value)] + [Polynomial()] * N


def sadd(a, b):
    return [x+y for x, y in zip(a, b)]


def sscale(a, value):
    return [x*value for x in a]


def smul(a, b):
    return [sum((a[i]*b[n-i] for i in range(n+1)), Polynomial()) for n in range(len(a))]


def shift(a, k):
    return [Polynomial()] * k + a[:len(a)-k] if k else list(a)


def log_series(u):
    N = len(u)-1
    out = sconstant(0, N)
    power = sconstant(1, N)
    for k in range(1, N+1):
        power = smul(power, u)
        out = sadd(out, sscale(power, Q((-1)**(k+1), k)))
    return out


def negative_power_series(u, j):
    N = len(u)-1
    out = sconstant(1, N)
    power = sconstant(1, N)
    for k in range(1, N+1):
        power = smul(power, u)
        out = sadd(out, sscale(power, Q((-1)**k*math.comb(j+k-1, k))))
    return out


def root_residual(delta):
    N = len(delta)-1
    b, c, k, a, d, e, invlam, ell = [variable(i) for i in range(8)]
    u = shift(delta, 1)
    logu = log_series(u)
    ellu = sadd(sconstant(ell, N), logu)
    Qs = [sconstant(b, N), sadd(sscale(ellu, c), sconstant(k, N)),
          sadd(sadd(sscale(smul(ellu, ellu), a), sscale(ellu, d)), sconstant(e, N))]
    out = sadd([v.divide_lambda_inverse() for v in delta], sscale(logu, Q(-1, 2)))
    for j, Qj in enumerate(Qs, 1):
        out = sadd(out, sscale(shift(smul(negative_power_series(u, j), Qj), j), -1))
    return out


def solve_formal_inverse():
    delta = sconstant(0, 4)
    invlam = variable(6)
    for m in range(1, 4):
        residual = root_residual(delta)
        delta[m] = -invlam*residual[m]
    residual = root_residual(delta)
    for m in range(4):
        require(residual[m] == 0, "formal inverse residual coefficient " + str(m))
    for m in range(1, 4):
        require(all(key[7] <= m-1 for key in delta[m].terms), "formal inverse log degree")
    return delta[1:4], residual[4]



def verify_acceleration(data):
    N = 3
    ell, B2, aa, dd, ee = (variable(i) for i in (7, 2, 3, 4, 5))
    b, c = Q(1, 4), Q(-7, 540)
    t = sconstant(0, N)
    t[1] = Polynomial.constant(1)
    log1t = log_series(t)
    ellshift = sadd(sconstant(ell, N), log1t)
    P3 = aa*ell*ell+dd*ell+ee
    forward = [Polynomial.constant(1), Polynomial.constant(b), c*ell+B2, P3]
    shifted = sconstant(1, N)
    shifted = sadd(shifted, sscale(shift(negative_power_series(t, 1), 1), b))
    second = sadd(sscale(ellshift, c), sconstant(B2, N))
    shifted = sadd(shifted, shift(smul(negative_power_series(t, 2), second), 2))
    shifted = sadd(shifted, shift(sconstant(P3, N), 3))
    w = list(forward)
    w[0] = Polynomial()
    norm = [Polynomial.constant(v) for v in (1, Q(1, 2), Q(-1, 8), Q(1, 16))]
    ratio = smul(norm, smul(shifted, negative_power_series(w, 1)))
    expected = data["ratio"]
    require(ratio[0] == 1, "ratio constant")
    require(ratio[1] == rational(expected["first"], "ratio first"), "ratio first coefficient")
    require(ratio[2] == rational(expected["second"], "ratio second"), "ratio second coefficient")
    third = rational(expected["third_log"], "ratio log")*ell + rational(expected["third_rational"], "ratio rational") + rational(expected["third_B2"], "ratio B2")*B2
    require(ratio[3] == third, "ratio third coefficient")
    checks = 4
    for J in range(1, data["max_J"]+1):
        weights = (Q(1),)
        for j in range(1, J+1):
            r = Q(1, 2**j)
            factor = (-r/(1-r), 1/(1-r))
            for unused in range(max(1, j-1)):
                weights = mul(weights, factor)
        require(sum(weights, Q(0)) == 1, "accelerator preserves constants")
        if J == 3:
            require(weights == tuple(rational(x, "weight") for x in data["weights_J3"]), "five-point dyadic weights")
        for j in range(1, J+1):
            for k in range(max(1, j-1)):
                require(sum((w*Q(1, 2**(j*i))*i**k for i, w in enumerate(weights)), Q(0)) == 0,
                        "dyadic power-log annihilation")
                checks += 1
    return checks


def verify_fixture(d):
    validate_fixture(d)
    counts = {}
    l = d["log_models"]
    N, Qmax, Amax = (l[k] for k in ("n_max", "q_max", "a_max"))
    for q in range(Qmax+1):
        require(log_power_by_products(q, N) == log_power_by_symmetric(q, N), "log-power coefficient identity")
    counts["log_coefficients"] = (Qmax+1)*(N+1)
    for row in l["anchors"]:
        require(model(row["a"], row["q"], row["n"])[row["n"]] == rational(row["value"], "anchor"), "false log-model anchor")
    closure = 0
    for a in range(Amax+1):
        for q in range(1, Qmax+1):
            for b in range(Amax+1):
                # Several nontrivial logarithmic products, including q+s>q_max.
                s = 1 + (a+b+q) % Qmax
                require(convolution(model(a, q, N), model(b, s, N), N) == model(a+b, q+s, N), "basis product identity")
                closure += N+1
    counts["basis_product_coefficients"] = closure
    taylor_count = 0
    for row in d["signed_taylor"]["samples"]:
        v = [rational(x, "Taylor value") for x in row["values"]]
        n, i, M = (row[k] for k in ("n", "i", "order"))
        main = sum((Q((-1)**k*math.comb(i, k))*backward(v, n, k)
                    for k in range(min(M-1, i)+1)), Q(0))
        rest = sum((Q((-1)**M*math.comb(i-1-r, M-1))*backward(v, n-r, M)
                    for r in range(i-M+1)), Q(0)) if i >= M else Q(0)
        require(main+rest == v[n-i] == rational(row["expected"], "Taylor expected"), "signed discrete Taylor identity")
        weights = sum((math.comb(i-1-r, M-1) for r in range(i-M+1)), 0) if i >= M else 0
        require(weights == (math.comb(i, M) if i >= M else 0), "Taylor remainder weight sum")
        taylor_count += 2
    counts["signed_Taylor_identities"] = taylor_count
    inv = d["inverse"]
    unit_checks = 0
    for m in range(inv["unit_max"]+1):
        Nunit = m+3
        integral = [Q(0)]*(Nunit+1)
        for a in range(m+1):
            basis = model(a+1, 0, Nunit)
            coefficient = -Q((-1)**a*math.comb(m, a), a+3)
            integral = [x+coefficient*y for x, y in zip(integral, basis)]
        for n in range(1, Nunit+1):
            weight = Q(1, n+2) if n == m+1 else Q(0)
            if n <= m:
                weight -= Q(2*(n+1), (m+1)*(m+2)*(m+3))
            require(integral[n] == weight, "unit-vector inverse identity")
            unit_checks += 1
    counts["unit_inverse_coefficients"] = unit_checks
    tail_checks = 0
    K = inv["tail_end"]
    for row in inv["models"]:
        a, q = row["a"], row["q"]
        h, y = model(a, q, K+1), inverse_model(a, q, K+1)
        require(y[0] == rational(row["critical_constant"], "critical constant"), "false critical constant")
        # Exact symbolic derivative of the u-polynomial/log antiderivative:
        # d/du [u^(a+3) sum_j q!/(q-j)! L^(q-j)/(a+3)^(j+1)] = u^(a+2)L^q.
        cs = [Q(math.factorial(q), math.factorial(q-j)*(a+3)**(j+1)) for j in range(q+1)]
        require((a+3)*cs[0] == 1, "antiderivative leading term")
        for j in range(1, q+1):
            require((a+3)*cs[j] == (q-j+1)*cs[j-1], "antiderivative cancellation")
        for n in range(K+1):
            prior = h[n-1] if n else Q(0)
            require((n+1)*y[n+1]-(n+2)*y[n] == h[n]-prior, "inverse coefficient equation")
            tail_checks += 1
        for n in range(1, K+1):
            finite = h[n-1]/(n+2)-2*(n+1)*sum((h[k]/((k+1)*(k+2)*(k+3)) for k in range(n, K+1)), Q(0))
            boundary = Q(n+1, K+2)*(h[K]/(K+3)-y[K+1])
            require(finite-y[n] == boundary, "finite inverse tail with exact boundary term")
            tail_checks += 1
    counts["log_inverse_coefficient_and_tail_identities"] = tail_checks
    computed = kernel_values()
    for name in KERNEL_KEYS:
        require(computed[name] == rational(d["kernel"][name], name), "false kernel/third-order constant: " + name)
    counts["kernel_and_third_order_constants"] = len(KERNEL_KEYS)
    # Algebraic K_x rearrangement, with C = C1/3 -2 L1/9 -1/12.
    # Compare coefficients of independent C1,D,L1,L2,1 after substitution.
    lhs = (Q(1, 3), Q(1, 2), Q(-17, 36), Q(-1, 8), Q(-1, 16))
    rhs = (Q(1, 3), Q(1, 2), -Q(2, 9)-Q(1, 4), Q(-1, 8), -Q(1, 12)+Q(1, 48))
    require(lhs == rhs, "K_x inverse index rearrangement")
    moments = 0
    for M, expected in zip(d["moments"]["orders"], d["moments"]["counts"]):
        triples = [(k, p, q) for p in range(1, M+1) for q in range(1, p+1) for k in range(M-p+1)]
        require(len(triples) == expected == M*(M+1)*(M+2)//6, "false scalar moment count")
        require(len(set(triples)) == len(triples), "duplicate indexed moment")
        for k, p, q in triples:
            require(k <= M-1 and M+1-k >= 2 and k+p-1 <= M-1, "moment exponent accounting")
        moments += len(triples)
    counts["scalar_moment_indices"] = moments
    actual, residual4 = solve_formal_inverse()
    for m, poly in enumerate(actual, 1):
        expected = Polynomial({tuple(t["powers"]): rational(t["coefficient"], "inverse term") for t in d["formal_inverse"]["R"+str(m)]})
        require(poly == expected, "false formal inverse R" + str(m))
    require(residual4 != 0, "uncomputed fourth inverse term was accidentally treated as zero")
    counts["formal_inverse_orders"] = 3
    # Newton exponent recurrence is algebra, not a convergence proof.
    exponent = 1
    for k in range(8):
        require(exponent == 3*2**k-2, "Newton exponent identity")
        exponent = 2*exponent+2
    counts["Newton_exponent_identities"] = 8
    interval_checks = 0
    negative_numerator = False
    for row in d["synthetic_intervals"]:
        z = rational(row["z"], "z")
        al, ah = interval(row["a"], "a")
        vl, vh = interval(row["v"], "v")
        Cl, Ch = interval(row["C"], "C")
        bounds = {"A": (z+vl, z+vh), "B": (z+vl/ah, z+vh/al),
                  "P": (z+vl/ah-Ch/al**2, z+vh/al-Cl/ah**2)}
        for key, value in bounds.items():
            require(value == interval(row["expected"][key], "expected"), "false interval endpoint")
        for a in (al, (al+ah)/2, ah):
            for v in (vl, (vl+vh)/2, vh):
                for C in (Cl, (Cl+Ch)/2, Ch):
                    values = {"A": z+v, "B": z+v/a, "P": z+(v-C/a)/a}
                    negative_numerator = negative_numerator or v-C/a < 0
                    for key in bounds:
                        require(bounds[key][0] <= values[key] <= bounds[key][1], "interval inclusion failure")
                        interval_checks += 1
    require(negative_numerator, "fixtures must include negative refined numerator")
    require(Q(44, 7)*Q(797, 2000)**2 == Q(6987299, 7000000) < 1, "rational a lower-bound comparison")
    require(Q(5, 4)*(1-Q(797, 2000)) == Q(1203, 1600) < Q(94, 125), "rational contraction comparison")
    require(Q(61, 80)+Q(1, 50) == Q(313, 400) < Q(4, 5), "outward error contraction budget")
    for L, U in ((Q(125, 79), Q(1000, 527)), (Q(1, 100), Q(10)), (Q(2), Q(5, 2))):
        w = U-L
        d0 = min(w/4, L/2)
        z, t = L-d0, L-d0/2
        require(0 < z < t < L <= U and z >= L/2, "strict interior witness")
        require(1/L-1/U == w/(L*U), "reciprocal bracket width")
        for a in (Q(2, 5), Q(1, 2), Q(3, 4)):
            s = d0/w
            for j in range(61):
                T = Q(j, 40)
                lo, hi = max(Q(0), T-s), min(Q(1), T/a-s)
                if lo <= hi:
                    require(hi-lo <= (1+s)*(1-a) <= Q(5, 4)*(1-a), "coarse intersection geometry")
                    interval_checks += 1
    counts["synthetic_interval_and_geometry_checks"] = interval_checks
    counts["ratio_and_acceleration_identities"] = verify_acceleration(d["acceleration"])
    canonical = json.dumps(d, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("ascii")
    return {"schema": "report146-exact-receipt-v1", "status": "passed", "scope": SCOPE,
            "analytic_inputs": list(INPUT_LABELS), "fixture_canonical_sha256": hashlib.sha256(canonical).hexdigest(),
            "checks": counts, "computed_kernel": {k: qstr(v) for k, v in computed.items()},
            "no_analytic_or_numerical_certification": True}


def leaf_name(value):
    require(type(value) is str and re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_-]{0,63}\.json", value) is not None,
            "use a simple .json filename in the companion directory (no path components)")
    return value


def secure_directory(path):
    require(os.name == "posix" and hasattr(os, "O_NOFOLLOW") and hasattr(os, "O_DIRECTORY"), "POSIX no-follow support required")
    require(os.open in os.supports_dir_fd, "directory-descriptor open support required")
    path = Path(path)
    require(path.is_absolute() and ".." not in path.parts, "absolute nontraversing directory required")
    fd = os.open("/", os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        for part in path.parts[1:]:
            nxt = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=fd)
            os.close(fd)
            fd = nxt
        return fd
    except BaseException:
        os.close(fd)
        raise


def read_local(name):
    name = leaf_name(name)
    directory = secure_directory(ROOT)
    fd = None
    try:
        fd = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=directory)
        st = os.fstat(fd)
        require(stat.S_ISREG(st.st_mode), "fixture must be a regular file")
        require(st.st_size <= MAX_BYTES, "fixture exceeds byte bound")
        out = b""
        while True:
            block = os.read(fd, min(8192, MAX_BYTES+1-len(out)))
            if not block:
                break
            out += block
            require(len(out) <= MAX_BYTES, "fixture exceeds byte bound")
        return out
    finally:
        if fd is not None:
            os.close(fd)
        os.close(directory)


def write_local(name, payload):
    name = leaf_name(name)
    require(type(payload) is bytes and len(payload) <= MAX_BYTES, "receipt byte bound exceeded")
    directory = secure_directory(ROOT)
    fd = None
    try:
        fd = os.open(name, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600, dir_fd=directory)
        view = memoryview(payload)
        while view:
            written = os.write(fd, view)
            require(written > 0, "incomplete receipt write")
            view = view[written:]
        os.fsync(fd)
    finally:
        if fd is not None:
            os.close(fd)
        os.close(directory)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixture", default="fixture.json", help="simple JSON filename in this companion directory")
    parser.add_argument("--output", help="create a NEW JSON receipt in this companion directory; never overwrite")
    args = parser.parse_args(argv)
    try:
        data = parse_json(read_local(args.fixture))
        receipt = verify_fixture(data)
        receipt["implementation_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
        receipt["python_optimization"] = sys.flags.optimize
        payload = (json.dumps(receipt, indent=2, sort_keys=True)+"\n").encode("ascii")
        if args.output is not None:
            write_local(args.output, payload)
        sys.stdout.write(payload.decode("ascii"))
        return 0
    except (CheckError, OSError) as exc:
        sys.stderr.write("verification failed: " + str(exc) + "\n")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())

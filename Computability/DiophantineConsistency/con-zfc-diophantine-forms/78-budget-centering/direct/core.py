"""Small exact arithmetic utilities; no third-party dependencies."""
from collections import defaultdict
from math import prod


def pconst(n):
    return {(): n} if n else {}


def pvar(name):
    return {(name,): 1}


def padd(a, b):
    out = dict(a)
    for key, value in b.items():
        out[key] = out.get(key, 0) + value
    return {key: value for key, value in out.items() if value}


def pneg(a):
    return {key: -value for key, value in a.items()}


def psub(a, b):
    return padd(a, pneg(b))


def pmul(a, b):
    out = defaultdict(int)
    for ma, ca in a.items():
        for mb, cb in b.items():
            out[tuple(sorted(ma + mb))] += ca * cb
    return {key: value for key, value in out.items() if value}


def psos(polys):
    out = {}
    for poly in polys:
        out = padd(out, pmul(poly, poly))
    return out


def pdegree(poly):
    return max(map(len, poly), default=-1)


def rows(poly):
    return [{"monomial": list(m), "coefficient": c}
            for m, c in sorted(poly.items())]


def parse(poly_rows):
    out = {}
    for term in poly_rows:
        m = tuple(sorted(term["monomial"]))
        out[m] = out.get(m, 0) + term["coefficient"]
    return {m: c for m, c in out.items() if c}


def peval(poly_rows, env):
    return sum(term["coefficient"] * prod(env[v] for v in term["monomial"])
               for term in poly_rows)


def poly_product_factors(labels, normalized=False):
    """Ascending univariate coefficients of product (X+j), or (1+jX)."""
    result = [1]
    for label in labels:
        const, slope = (1, label) if normalized else (label, 1)
        out = [0] * (len(result) + 1)
        for i, coefficient in enumerate(result):
            out[i] += const * coefficient
            out[i + 1] += slope * coefficient
        while len(out) > 1 and out[-1] == 0:
            out.pop()
        result = out
    return result


def poly_eval(coefficients, value):
    result = 0
    for coefficient in reversed(coefficients):
        result = result * value + coefficient
    return result


def budget_factor(premises, conclusion):
    return prod(1 + p for p in premises) + conclusion


def finite_closure(rules):
    """rules is a list of (tuple of actual premises, conclusion)."""
    derived = set()
    while True:
        extended = derived | {c for premises, c in rules
                              if all(p in derived for p in premises)}
        if extended == derived:
            return derived
        derived = extended


def flow_balance(rules, target=1):
    out = defaultdict(int)
    out[target] -= 1
    for premises, c in rules:
        out[c] += 1
        for p in premises:
            out[p] -= 1
    return {label: value for label, value in out.items() if value}


def make_certificate(expansion_order, target=1):
    """Construct after choosing a genuine top-down proof-tree expansion.

    All scales are chosen in a noncircular order: label list, budget, M,
    then the obligation accumulator.  Zero labels are ordinary obligations.
    """
    if type(target) is not int or target != 1:
        raise ValueError("This optimized budget is specialized to target 1")
    budget = [1]
    for premises, c in expansion_order:
        if (len(premises) > 2 or type(c) is not int or c < 0
                or any(type(p) is not int or p < 0 for p in premises)):
            raise ValueError("invalid natural Horn rule")
        budget.append(budget[-1] * budget_factor(premises, c))
    base = budget[-1] + 1
    frontier = [target]
    accumulator = [base + target]
    for premises, c in expansion_order:
        if c not in frontier:
            raise ValueError("not a top-down proof-tree expansion")
        frontier.remove(c)
        frontier.extend(premises)
        numerator = accumulator[-1] * prod(base + p for p in premises)
        quotient, remainder = divmod(numerator, base + c)
        if remainder:
            raise AssertionError("frontier divisibility failed")
        accumulator.append(quotient)
        if quotient != prod(base + p for p in frontier):
            raise AssertionError("frontier product invariant failed")
    if frontier:
        raise ValueError("unfinished proof tree")
    return {"target": target, "M": base, "S": accumulator, "T": budget,
            "rules": [[list(premises), c] for premises, c in expansion_order]}


def validate_certificate(certificate):
    rules = [(tuple(p), c) for p, c in certificate["rules"]]
    s, t, m = certificate["S"], certificate["T"], certificate["M"]
    n = len(rules)
    if (type(certificate.get("target")) is not int
            or certificate["target"] != 1
            or len(s) != n + 1 or len(t) != n + 1):
        return False
    if any(type(v) is not int for v in [m] + s + t):
        return False
    if min([m] + s + t) < 0:
        return False
    if not (s[0] == m + 1 and s[-1] == 1 and t[0] == 1 and m == t[-1] + 1):
        return False
    for i, (premises, c) in enumerate(rules):
        if (len(premises) > 2
                or any(type(v) is not int or v < 0 for v in (c,) + premises)):
            return False
        if s[i + 1] * (m + c) != s[i] * prod(m + p for p in premises):
            return False
        if t[i + 1] != t[i] * budget_factor(premises, c):
            return False
    return True

#!/usr/bin/env python3
"""Exact finite audits supporting PROOF.md; Python standard library only.

Checks polynomial identities, source topology/liveness, complete fixed
payload hashes, centered leading forms and changed-polynomial degrees.
These are NOT tests of ZFC consistency or a substitute for the unbounded
Pell/source arguments in PROOF.md and the pinned parent proofs.
"""
import argparse
from collections import Counter
import gzip
import hashlib
import itertools
import json
from math import isqrt
from pathlib import Path
import random

ROOT = Path(__file__).resolve().parent


def require(value, label):
    if not value:
        raise AssertionError(label)


class Poly:
    """Tiny exact sparse integer polynomial, used only for finite identities."""
    def __init__(self, n, terms=None):
        self.n = n
        self.terms = {k: int(v) for k, v in (terms or {}).items() if v}

    @classmethod
    def const(cls, n, value):
        return cls(n, {(0,) * n: value})

    @classmethod
    def var(cls, n, index):
        key = [0] * n
        key[index] = 1
        return cls(n, {tuple(key): 1})

    def coerce(self, other):
        if isinstance(other, Poly):
            require(other.n == self.n, "polynomial rings agree")
            return other
        return Poly.const(self.n, other)

    def __add__(self, other):
        other = self.coerce(other)
        out = dict(self.terms)
        for key, value in other.terms.items():
            out[key] = out.get(key, 0) + value
        return Poly(self.n, out)

    __radd__ = __add__

    def __neg__(self):
        return Poly(self.n, {k: -v for k, v in self.terms.items()})

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) - self

    def __mul__(self, other):
        other = self.coerce(other)
        out = {}
        for ka, va in self.terms.items():
            for kb, vb in other.terms.items():
                key = tuple(a + b for a, b in zip(ka, kb))
                out[key] = out.get(key, 0) + va * vb
        return Poly(self.n, out)

    __rmul__ = __mul__

    def __pow__(self, power):
        require(isinstance(power, int) and power >= 0, "nonnegative exponent")
        result = Poly.const(self.n, 1)
        base = self
        while power:
            if power & 1:
                result = result * base
            power //= 2
            if power:
                base = base * base
        return result

    def __eq__(self, other):
        try:
            other = self.coerce(other)
        except (TypeError, ValueError):
            return False
        return self.terms == other.terms

    def degree(self, weights=None):
        weights = weights or [1] * self.n
        return max((sum(e * w for e, w in zip(k, weights)) for k in self.terms), default=-1)

    def leading(self, weights):
        degree = self.degree(weights)
        return Poly(self.n, {k: v for k, v in self.terms.items()
                             if sum(e * w for e, w in zip(k, weights)) == degree})

    def sha256(self):
        payload = json.dumps(sorted((list(k), v) for k, v in self.terms.items()), separators=(",", ":"))
        return hashlib.sha256(payload.encode()).hexdigest()


def norm(s, a, b, c):
    return ((s + c - a - b) ** 2 - 4 * (s * c + a * b)) ** 2 - 64 * s * c * a * b


def identity_audits():
    m, t = [Poly.var(2, k) for k in range(2)]
    parity = []
    for epsilon in (0, 1):
        x = 2 * m + epsilon
        h = t**2 * x * (x + 1) + t * x + m
        d = x * t * (x + 1) * (t * (x + 1) + 2) * (t**2 * x + 1)
        if epsilon == 0:
            lower = m * (2 * t**2 + 4 * (m + 1) * t - m)
            upper = 2 * m * (4 * m + 1) * t**2 - 4 * m**2 * t + (m + 1)**2
        else:
            lower = t**2 * x * (x + 2) + 2 * t * x * (m + 2) - m**2
            upper = (t * x - (m + 1))**2
        require(d - h**2 == lower, f"parity {epsilon}: lower identity")
        require((h + 1)**2 - d == upper, f"parity {epsilon}: upper identity")
        # Positive coefficient certificates after m=1+u,t=1+v.
        mp, tp = m + 1, t + 1
        xp = 2 * mp + epsilon
        hp = tp**2 * xp * (xp + 1) + tp * xp + mp
        dp = xp * tp * (xp + 1) * (tp * (xp + 1) + 2) * (tp**2 * xp + 1)
        for label, polynomial in [("lower", dp - hp**2), ("upper", (hp + 1)**2 - dp)]:
            require(all(v >= 0 for v in polynomial.terms.values()), label + " coefficient positivity")
            require(polynomial.terms.get((0, 0), 0) > 0, label + " positive constant")
        parity.append({"epsilon": epsilon, "lower_terms": len(lower.terms), "upper_terms": len(upper.terms)})

    s, a, b, c = [Poly.var(4, k) for k in range(4)]
    d = s - c
    e1 = d**2 - 2 * (s + c) * (a + b) + (a - b)**2
    e9 = d**2 - 2 * (s + c) * (9 * a + b) + (9 * a - b)**2
    require(norm(s, a, b, c) == e1**2 - 64 * s * c * a * b, "centered norm")
    require(e9 - e1 == 16 * a * (5 * a - (s + b + c)), "bracket difference")
    difference = 16 * a * (5 * a - (s + b + c)) * (e9 + e1) - 512 * s * c * a * b
    require(norm(s, 9 * a, b, c) - norm(s, a, b, c) == difference, "whole norm difference")

    z, r1, r2, r3 = [Poly.var(4, k) for k in range(4)]
    product = Poly.const(4, 1)
    for signs in itertools.product((-1, 1), repeat=3):
        product = product * (z + signs[0] * r1 + signs[1] * r2 + signs[2] * r3)
    require(product == norm(z**2, r1**2, r2**2, r3**2), "eight radical factors")

    q, v, mm, z0 = [Poly.var(4, k) for k in range(4)]
    delta = q - 1
    lhs = delta * (mm * v + z0)**2 - mm**2 * (q * v**2 - 1)
    rhs = delta * z0**2 + 2 * delta * mm * v * z0 + mm**2 * (1 - v**2)
    require(lhs == rhs, "exact center cancellation")

    ss = Poly.var(1, 0)
    traces = [Poly.const(1, 1), ss]
    ordinates = [Poly.const(1, 0), Poly.const(1, 1)]
    for _ in range(4):
        traces.append(2 * ss * traces[-1] - traces[-2])
        ordinates.append(2 * ss * ordinates[-1] - ordinates[-2])
    require(traces[3] == ss * (4 * ss**2 - 3), "auxiliary index3 identity")
    require(traces[5] == ss * (16 * ss**4 - 20 * ss**2 + 5), "auxiliary index5 identity")
    require(ordinates[3] == 4 * ss**2 - 1, "main index3 identity")
    qq = ss + 3
    gap = 16 * qq**2 - 20 * qq + 5 - 8 * qq**2
    require(all(value > 0 for value in gap.terms.values()), "fifth-index strict gap for Q>=3")
    da, ii = Poly.var(2, 0) + 24, Poly.var(2, 1) + 9
    for label, polynomial in [
        ("Q>Df", da**2 * ii**2 - (1 + da * ii**2)),
        ("Q-1>2Df", da**2 * ii**2 - 1 - 2 * (1 + da * ii**2)),
    ]:
        require(all(value > 0 for value in polynomial.terms.values()), label + " positive polynomial certificate")
        require(polynomial.terms.get((0, 0), 0) > 0, label + " positive constant")

    grid_count = 0
    for xi in range(2, 129):
        for ti in range(1, 129):
            di = xi * ti * (xi + 1) * (ti * (xi + 1) + 2) * (ti * ti * xi + 1)
            hi = ti * ti * xi * (xi + 1) + ti * xi + xi // 2
            require(hi * hi < di < (hi + 1) * (hi + 1), "small square-gap instance")
            require(isqrt(di) == hi, "small exact square root floor")
            grid_count += 1
    return {"parity_identities": parity, "positive_coefficient_certificates": True,
            "norm_factorization": True, "center_identity": True,
            "weight_difference_identity": True, "square_gap_grid_cases": grid_count,
            "auxiliary_index1_3_5_formulas": True, "auxiliary_gap_positive_certificates": True}


class Lead:
    """A certified top homogeneous part, failing if an addition cancels it.

The explicit center identity is required where cancellation really occurs.
This prevents a gate-wise degree upper bound from masquerading as an exact
degree calculation.
"""
    def __init__(self, polynomial, weights):
        self.p = polynomial
        self.weights = weights

    def coerce(self, other):
        return other if isinstance(other, Lead) else Lead(Poly.const(self.p.n, other), self.weights)

    @property
    def degree(self):
        return self.p.degree(self.weights)

    def __neg__(self):
        return Lead(-self.p, self.weights)

    def __add__(self, other):
        other = self.coerce(other)
        if not self.p.terms:
            return other
        if not other.p.terms:
            return self
        if self.degree > other.degree:
            return self
        if other.degree > self.degree:
            return other
        pp = self.p + other.p
        require(bool(pp.terms), "unhandled leading cancellation; explicit identity required")
        return Lead(pp, self.weights)

    __radd__ = __add__

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) - self

    def __mul__(self, other):
        other = self.coerce(other)
        return Lead(self.p * other.p, self.weights)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        return Lead(self.p**exponent, self.weights)


def degree_audit(eq, direct):
    auxiliary_gap = eq.get("transport_majorant") == "b"
    names = eq["witnesses"] + eq["fixed_numerals"]
    weights = [1] * len(eq["witnesses"]) + [0] * len(eq["fixed_numerals"])
    variables = {name: Poly.var(len(names), i) for i, name in enumerate(names)}
    r = {name: Lead(poly, weights) for name, poly in variables.items()}

    def val(token):
        return r[token] if isinstance(token, str) else Lead(Poly.const(len(names), token), weights)

    # Stop before norm-tail cancellation; use the exact identity audited above.
    for target, op, left, right in eq["source"]:
        if target == "U":
            break
        aa, bb = val(left), val(right)
        r[target] = {"+": lambda: aa + bb, "-": lambda: aa - bb, "*": lambda: aa * bb}[op]()
    z0 = r["P1mu2"] * (r["Hp"] * r["n"] + r["Kpos"]) + r["Hp"] * r["brk"]
    d = r["delta"] * z0**2 + 2 * r["delta"] * r["Mtot"] * r["V"] * z0 + r["M2"] * (1 - r["V"]**2)
    a, b, s, c = [r[name] for name in ("fa", "fb", "fs", "fc")]
    expected_degrees = ([68, 70, 96, 96, 80] if direct else [74, 76, 104, 104, 86]) if auxiliary_gap else (
        [68, 70, 96, 96, 85] if direct else [74, 76, 104, 104, 92])
    require([v.degree for v in (a, b, s, c, d)] == expected_degrees, "exact front degrees")
    require(s.p == c.p, "source center has equal top terms")
    if not auxiliary_gap:
        require(2 * d.degree > max((s.degree + b.degree), 2 * b.degree), "unique bracket leader")
        require(4 * d.degree > s.degree + c.degree + a.degree + b.degree, "unique norm leader")

    q0 = variables["beta"] * variables["J"]
    kval = variables["eta"] + variables["zeta"]
    if auxiliary_gap:
        common = variables["i"]**4 * variables["Y"]**16 * kval**8 * (q0 - variables["F"])**2
        if direct:
            x0 = q0 + variables["x"]
            b0 = (q0 * variables["K0"] + x0) * (q0 - variables["F"] - variables["alpha"]) - q0 * variables["F"]
            expected_d = -(2**5) * q0**40 * x0**8 * common * b0
            expected_c = 2**4 * q0**44 * x0**10 * variables["i"]**6 * variables["Y"]**22 * kval**12 * (q0 - variables["F"])**2
            expected_b = 2**4 * q0**34 * x0**8 * variables["i"]**4 * variables["Y"]**16 * kval**8
            beta_power = 156
            output_leader = "2^20*q0^156*(q0+x)^36*i^20*Y^76*(eta+zeta)^40*(q0-F)^4"
        else:
            expected_d = -(2**5) * q0**46 * variables["w"]**9 * common * (q0 - variables["F"] - variables["alpha"])
            expected_c = 2**4 * q0**52 * variables["w"]**10 * variables["i"]**6 * variables["Y"]**22 * kval**12 * (q0 - variables["F"])**2
            expected_b = 2**4 * q0**40 * variables["w"]**8 * variables["i"]**4 * variables["Y"]**16 * kval**8
            beta_power = 184
            output_leader = "2^20*q0^184*w^36*i^20*Y^76*(eta+zeta)^40*(q0-F)^4"
        require(d.p == expected_d, "full short-majorant center leader")
        require(c.p == expected_c, "full auxiliary radicand leader")
        require(b.p == expected_b, "full strong radicand leader")
        require(s.degree + b.degree > max(2 * d.degree, s.degree + a.degree, 2 * b.degree), "short-majorant bracket leader is -4*c0*b0")
        degree = 2 * (c.degree + b.degree)
        require(degree > s.degree + c.degree + a.degree + b.degree, "unique short-majorant output leader")
        require(degree == eq["exact_degree"], "short-majorant exact norm degree")
        diff_degree = a.degree + 2 * c.degree + b.degree
        require(diff_degree == eq["weighted_minus_equal_weight_exact_degree"], "same-majorant weight difference degree")
        # The exact difference identity has two top contributions, +256 and
        # -512 times a0*c0^2*b0, leaving -256 times that nonzero product.
        require(a.degree < b.degree, "nonzero weight difference leader after explicit cancellation")
        selected_output = {"J": beta_power, "beta": beta_power, "i": 20, "Y": 76, "eta": 40, "F": 4}
        selected_output["x" if direct else "w"] = 36
        return {"front_degrees_a_b_s_c_d": expected_degrees, "Z0_degree": z0.degree,
                "exact_degree": degree, "weighted_minus_unweighted_exact_degree": diff_degree,
                "full_center_leader_terms": len(d.p.terms), "full_center_leader_sha256": d.p.sha256(),
                "output_leader_type": "16*fc0^2*fb0^2", "full_output_leader": output_leader,
                "selected_output_monomial": selected_output, "selected_output_coefficient_symbolic_ports": 2**20,
                "full_norm_selected_coefficient": f"2^20 * beta^{beta_power}",
                "difference_leader": "-256*a0*c0^2*b0 (nonzero)"}
    if direct:
        x0 = q0 + variables["x"]
        b0 = (q0 * variables["K0"] + x0) * (q0 - variables["F"] - variables["alpha"]) - q0 * variables["F"]
        expected = 2**7 * q0**39 * x0**9 * variables["i"]**5 * variables["Y"]**19 * kval**10 * b0 * (q0 - variables["F"])
        selected = {"J": 39, "beta": 39, "x": 10, "i": 5, "Y": 19, "eta": 10, "alpha": 1, "F": 1}
    else:
        expected = 2**7 * q0**46 * variables["i"]**5 * variables["w"]**10 * variables["Y"]**19 * kval**10 * (q0 - variables["F"] - variables["alpha"]) * (q0 - variables["F"])
        selected = {"J": 46, "beta": 46, "w": 10, "i": 5, "Y": 19, "eta": 10, "alpha": 1, "F": 1}
    require(d.p == expected, "full exact centered leading form")
    target = tuple(selected.get(name, 0) for name in names)
    require(d.p.terms.get(target) == 2**7, "selected leading coefficient")
    alpha_index, f_index = names.index("alpha"), names.index("F")
    require(all(k[alpha_index] <= 1 for k in d.p.terms), "alpha exposed face")
    require(all(k[f_index] <= 1 for k in d.p.terms if k[alpha_index] == 1), "F exposed face")
    if direct:
        x_index = names.index("x")
        require(max(k[x_index] for k in d.p.terms) == 10, "highest direct x exponent")
    # P9-P1 has unique leading term -64*a0*c0*d0^2.
    diff_degree = a.degree + c.degree + 2 * d.degree
    require(diff_degree > s.degree + c.degree + a.degree + b.degree, "difference leader beats last product")
    require(a.degree + c.degree > 2 * a.degree, "difference bracket leader")
    require(diff_degree == eq["weighted_minus_equal_weight_exact_degree"], "difference exact degree")
    require(4 * d.degree == eq["exact_degree"], "full norm exact degree")
    return {"front_degrees_a_b_s_c_d": expected_degrees, "Z0_degree": z0.degree,
            "exact_degree": 4 * d.degree, "weighted_minus_unweighted_exact_degree": diff_degree,
            "full_center_leader_terms": len(d.p.terms), "full_center_leader_sha256": d.p.sha256(),
            "selected_center_monomial": selected, "selected_center_coefficient": 128,
            "full_norm_selected_coefficient": f"2^28 * beta^{156 if direct else 184}",
            "difference_leader": "-64*a0*c0*d0^2 (nonzero)"}


def topology(eq):
    available = set(eq["witnesses"]) | set(eq["fixed_numerals"])
    definitions = {}
    for row in eq["source"]:
        target, op, left, right = row
        require(target not in available, "unique output " + target)
        require(op in ("+", "-", "*"), "paid binary operation")
        for token in (left, right):
            require(isinstance(token, int) or token in available, "topological operand")
        available.add(target)
        definitions[target] = row
    live = set()
    stack = [eq["output"]]
    while stack:
        token = stack.pop()
        if not isinstance(token, str) or token in live:
            continue
        live.add(token)
        if token in definitions:
            stack.extend(definitions[token][2:])
    require(set(definitions) <= live, "all paid rows live")
    require(set(eq["witnesses"]) <= live, "all ten coordinates live")
    require(set(eq["fixed_numerals"]) <= live, "all four ports live")
    counts = dict(Counter(row[1] for row in eq["source"]))
    require(counts == eq["operation_breakdown"], "operation breakdown")
    require(len(definitions) == eq["operations"], "total operation count")
    return counts


def load_coefficients(eq):
    coefficients, hashes = {}, {}
    for name, metadata in eq["coefficient_binding"]["ports"].items():
        data = (ROOT / "coefficients" / metadata["file"]).read_bytes()
        raw = gzip.decompress(data)
        require(hashlib.sha256(data).hexdigest() == metadata["gzip_sha256"], "complete gzip hash " + name)
        require(hashlib.sha256(raw).hexdigest() == metadata["raw_sha256"], "complete raw hash " + name)
        value = int.from_bytes(raw, "little")
        require(value.bit_length() == metadata["bits"], "coefficient bit count " + name)
        coefficients[name] = value
        hashes[name] = {"bits": value.bit_length(), "raw_sha256": metadata["raw_sha256"]}
    require(coefficients["beta"] >= 31 and coefficients["beta"] % 2 == 1, "beta domain")
    require(coefficients["K0"] > 0, "K0 domain")
    require(0 < coefficients["MC"] < coefficients["beta"] < coefficients["MF"] < 2 * coefficients["beta"], "mask box")
    return coefficients, hashes


def evaluate(eq, inputs, coefficients, modulus):
    r = {name: value % modulus for name, value in (coefficients | inputs).items()}
    for target, op, left, right in eq["source"]:
        aa = r[left] if isinstance(left, str) else left
        bb = r[right] if isinstance(right, str) else right
        r[target] = {"+": lambda: aa + bb, "-": lambda: aa - bb, "*": lambda: aa * bb}[op]() % modulus
    return r


def equation_audit(filename, direct):
    eq = json.loads((ROOT / filename).read_text())
    raw_parent = (ROOT / eq["parent_local_file"]).read_bytes()
    require(hashlib.sha256(raw_parent).hexdigest() == eq["parent_sha256"], "whole pinned parent circuit")
    parent = json.loads(raw_parent)
    expected = [(["fa", "*", "dM2", "Dtau"] if row[0] == "fa" else row)
                for row in parent["source"] if row[0] != "Dtau9"]
    if eq.get("transport_majorant") == "b":
        expected = [([row[0], row[1], row[2], "cTR"] if row[0] == "qm1L" else row)
                    for row in expected if row[0] not in ("HI", "L")]
        parent = dict(parent)
        parent["source"] = [([row[0], row[1], row[2], "cTR"] if row[0] == "qm1L" else row)
                            for row in parent["source"] if row[0] not in ("HI", "L")]
    require(eq["source"] == expected, "exact one-row deletion and redirection")
    counts = topology(eq)
    coefficients, hashes = load_coefficients(eq)
    rng = random.Random(20261024 + int(direct))
    nonidentity = None
    cases = 0
    for modulus in (2**61 - 1, 2**127 - 1):
        for _ in range(16):
            inputs = {name: rng.randrange(1, 1000) for name in eq["witnesses"]}
            r = evaluate(eq, inputs, coefficients, modulus)
            rp = evaluate(parent, inputs, coefficients, modulus)
            require(r["N"] == norm(r["fs"], r["fa"], r["fb"], r["fc"]) % modulus, "independent tail evaluator")
            require(rp["N"] == norm(r["fs"], 9 * r["fa"], r["fb"], r["fc"]) % modulus, "weighted parent tail")
            if nonidentity is None and r["N"] != rp["N"]:
                nonidentity = {"modulus": str(modulus), "inputs": inputs,
                               "unweighted": str(r["N"]), "weighted": str(rp["N"])}
            cases += 1
    require(nonidentity is not None, "different polynomial at actual complete coefficient tuple")
    return {"operations": eq["operations"], "breakdown": counts, "all_rows_and_leaves_live": True,
            "fixed_coefficients": hashes, "degree": degree_audit(eq, direct),
            "modular_tail_cases": cases, "different_polynomial_witness": nonidentity}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = {"scope": "Exact finite algebra/circuit audits; unbounded equivalence is proved in PROOF.md.",
              "identities": identity_audits(),
              "equation98": equation_audit("equation98.json", False),
              "equation104": equation_audit("equation104.json", True),
              "equation96": equation_audit("equation96.json", False),
              "equation102": equation_audit("equation102.json", True)}
    data = (json.dumps(result, indent=2, sort_keys=True) + "\n").encode()
    path = ROOT / "CHECKS.json"
    if args.check:
        require(path.read_bytes() == data, "deterministic check receipt")
    else:
        path.write_bytes(data)
    print(json.dumps({"identities": "pass", **{key: result[key]["degree"]
                      for key in ("equation98", "equation104", "equation96", "equation102")}}, indent=2))


if __name__ == "__main__":
    main()

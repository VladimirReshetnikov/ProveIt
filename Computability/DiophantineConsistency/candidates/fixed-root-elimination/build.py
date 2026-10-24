#!/usr/bin/env python3
"""Materialize two fixed-blank root eliminations; no frozen helper is run."""
import argparse
from collections import Counter
import copy
import gzip
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
PARENT = ROOT / "con-zfc-diophantine-forms/36-small-tuple/baseline/product67.json"
COEFFICIENTS = ROOT / "con-zfc-diophantine-forms/36-small-tuple/coefficients"
PARENT_SHA = "732fecec5df8fecf98019f9aeadab7a63579c3ebfe6c179cbd7027dee24e9d08"


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def encode(value):
    return (json.dumps(value, indent=2) + "\n").encode()


def retained(parent):
    dependent, rows = {"f"}, []
    for row in parent["source"]:
        if any(isinstance(v, str) and v in dependent for v in row[2:]):
            dependent.add(row[0])
        else:
            rows.append(row)
    require(len(rows) == 50, "literal50-row retained prefix")
    return rows, dependent


def candidate(parent, unit):
    rows, dependent = retained(parent)
    prefix = "unit" if unit else "field"
    def n(name):
        return prefix + "_" + name
    def emit(name, op, left, right):
        rows.append([n(name), op, left, right])
        return n(name)
    k = emit("k", "*", "i", "c2")
    dm = emit("Dm1", "*", k, "aux_coefficient_root")
    d = emit("D", "+", dm, 1)
    rd = emit("RD", "*", "r_lhs", d)
    b = emit("b", "+", "R10a", rd)
    u = emit("u", "*", "R10a", "T")
    u2 = emit("u2", "*", u, u)
    p = emit("p", "*", d, u2)
    b2 = emit("b2", "*", b, b)
    pa = emit("Pa", "*", "norm_pair", "norm_index")
    pf = emit("P", "*", pa, "norm_transport")
    if not unit:
        c = emit("C", "*", pf, "R16")
        ll = emit("L", "*", c, p)
        mm = emit("M", "*", c, b2)
        pc = emit("Pc", "-", pf, c)
        zz = emit("Z", "*", pc, "aux_y2")
        lm = emit("LM", "+", ll, mm)
        lmz = emit("LMZ", "+", lm, zz)
        aa = emit("alpha", "-", lmz, 1)
        aa2 = emit("alpha2", "*", aa, aa)
        cross = emit("cross", "*", ll, mm)
        four = emit("four", "*", 4, cross)
        out = emit("out", "-", aa2, four)
    else:
        ss = emit("sum", "+", p, b2)
        gap = emit("gap", "-", ss, "aux_y2")
        qgap = emit("Qgap", "*", "R16", gap)
        ap = emit("Aplus1", "+", qgap, "aux_y2")
        aa = emit("A", "-", ap, 1)
        qp = emit("Qp", "*", "R16", p)
        qb = emit("Qb2", "*", "R16", b2)
        cross = emit("cross", "*", qp, qb)
        four = emit("four", "*", 4, cross)
        a2 = emit("A2", "*", aa, aa)
        kk = emit("K", "-", a2, four)
        uu = emit("guard", "+", kk, 1)
        pp = emit("product", "*", pf, uu)
        out = emit("out", "-", pp, 1)
    return dict(name="fixed_blank_root_elimination_" + ("unit75" if unit else "field73"),
                witness_domain="strictly positive integers",
                witnesses=[v for v in parent["witnesses"] if v != "f"],
                fixed_numerals=parent["fixed_numerals"], source=rows, output=out,
                exact_degree=293 if unit else 342,
                coefficient_binding=dict(file="../../con-zfc-diophantine-forms/36-small-tuple/coefficients/COEFFICIENT_BINDING.json",
                                         aliases=dict(beta="beta", K0="K", MC="MC", MF="MF_source"),
                                         warning="Use this complete tuple; MF_source is already shifted."),
                provenance=dict(parent=str(PARENT.relative_to(ROOT)), parent_sha256=PARENT_SHA,
                                unchanged_f_independent_rows=50, removed_rows=sorted(dependent - {"f"})),
                proof_boundary="Ordinary signed-T and root-elimination proofs in PROOF.md; independent review pending; no new Lean/internal-ZFC certificate.")


def fixed_values():
    path = COEFFICIENTS / "COEFFICIENT_BINDING.json"
    binding = json.loads(path.read_text())
    values, pins = {}, {}
    aliases = dict(beta="beta", K="K0", MC="MC", MF_source="MF")
    for item in binding["materialization"]["files"]:
        compressed = (COEFFICIENTS / item["file"]).read_bytes()
        raw = gzip.decompress(compressed)
        require(sha(compressed) == item["gzip_sha256"] and sha(raw) == item["sha256"], "actual port payload hash")
        value = int.from_bytes(raw, "little")
        require(value.bit_length() == item["bits"], "actual port size")
        values[aliases[item["port"]]] = value
        pins[item["port"]] = dict(raw_sha256=sha(raw), gzip_sha256=sha(compressed))
    d = binding["d"]
    base, low, high = values["beta"] + 1, values["MC"], values["MF"] - values["beta"]
    require(base == 1 << d and d >= 4 and values["K0"] > 0, "base and transport port")
    require(0 < low < base - 1 and 0 < high < base - 1, "native mask bounds")
    require(low % 4 == 2 and high % 8 == 4, "native mask low residues")
    require(low.bit_count() + high.bit_count() == d, "native mask population")
    return values, dict(binding_sha256=sha(path.read_bytes()), payloads=pins,
                        d=d, low_mod4=low % 4, native_high_mod8=high % 8,
                        population_sum=d, MF_shift_verified=True)


def topology(body):
    available = set(body["witnesses"] + body["fixed_numerals"])
    producers, costs = {}, Counter()
    for row in body["source"]:
        name, op, left, right = row
        require(name not in available and op in ("+", "-", "*"), "fresh binary producer")
        for value in (left, right):
            require(type(value) is int or value in available, "backward references")
        producers[name] = [v for v in (left, right) if isinstance(v, str)]
        available.add(name)
        costs[op] += 1
    used, pending = set(), [body["output"]]
    while pending:
        value = pending.pop()
        if value not in used:
            used.add(value)
            pending.extend(producers.get(value, []))
    require(used == available, "all supplied and computed coordinates live")
    require(len(body["witnesses"]) == 14 and "f" not in available, "fourteen retained witnesses")
    return dict(operations=sum(costs.values()), operation_counts=dict(costs), witnesses=14,
                fixed_ports=4, all_rows_and_ports_live=True)


def degree_certificate(body, fixed):
    # The only cancellation missed by naive propagation is norm_main.
    # Its full polynomial expansion and literal producer bindings are proved
    # in PROOF.md; its unique leading term is2*a*c*gam, of degree18.
    degrees = {name: 1 for name in body["witnesses"]}
    degrees.update({name: 0 for name in body["fixed_numerals"]})
    def degree(value):
        return 0 if type(value) is int else degrees[value]
    for name, op, left, right in body["source"]:
        degrees[name] = degree(left) + degree(right) if op == "*" else max(degree(left), degree(right))
        if name == "norm_main":
            degrees[name] = 18
    require(degrees[body["output"]] == body["exact_degree"], "exact-degree upper bound")
    leading = []
    for prime in (1000000007, 1000000009, 998244353):
        slopes = {name: (index + 2) ** 2 + 1 for index, name in enumerate(body["witnesses"])}
        values = dict(slopes)
        values.update({name: value % prime for name, value in fixed.items()})
        def val(value):
            return value if type(value) is int else values[value]
        for name, op, left, right in body["source"]:
            if name == "norm_main":
                v = 2 * values["R12"] * values["R10a"] * values["gam"]
            elif op == "*":
                v = val(left) * val(right)
            elif degree(left) > degree(right):
                v = val(left)
            elif degree(right) > degree(left):
                v = val(right) * (-1 if op == "-" else 1)
            else:
                v = val(left) + (val(right) if op == "+" else -val(right))
            values[name] = v % prime
        require(values[body["output"]] != 0, "actual-coefficient leading term survives")
        leading.append(dict(prime=prime, slopes=slopes, coefficient=values[body["output"]]))
    return dict(degree=body["exact_degree"], register_degree_bounds=degrees,
                norm_main_expansion="X²+2acX+2gX+2acg+g²-Hc²",
                norm_main_unique_degree18_term="2*a*c*gam",
                actual_coefficient_degree_attainment=leading)


class Poly:
    """Tiny independent sparse integer-ring normalizer, nine cut atoms."""
    def __init__(self, value=0):
        self.terms = dict(value) if isinstance(value, dict) else ({(0,) * 9: value} if value else {})
    @staticmethod
    def atom(index):
        exponents = [0] * 9
        exponents[index] = 1
        return Poly({tuple(exponents): 1})
    def __add__(self, other):
        other = other if isinstance(other, Poly) else Poly(other)
        out = dict(self.terms)
        for exponent, coefficient in other.terms.items():
            out[exponent] = out.get(exponent, 0) + coefficient
        return Poly({e: c for e, c in out.items() if c})
    __radd__ = __add__
    def __neg__(self):
        return Poly({e: -c for e, c in self.terms.items()})
    def __sub__(self, other):
        return self + -(other if isinstance(other, Poly) else Poly(other))
    def __rsub__(self, other):
        return Poly(other) - self
    def __mul__(self, other):
        other = other if isinstance(other, Poly) else Poly(other)
        out = {}
        for a, x in self.terms.items():
            for b, y in other.terms.items():
                exponent = tuple(u + v for u, v in zip(a, b))
                out[exponent] = out.get(exponent, 0) + x * y
        return Poly({e: c for e, c in out.items() if c})
    __rmul__ = __mul__
    def __pow__(self, exponent):
        out = Poly(1)
        for _ in range(exponent):
            out *= self
        return out


def algebra_certificate(parent):
    delta, c, i, t, r, y, pair, index, transport = map(Poly.atom, range(9))
    q = (delta * i * c ** 2) ** 2
    d = 1 + delta * i ** 2 * c ** 4
    b, u = c + r * d, c * t
    a = q * (d * u ** 2 + b ** 2) - (q - 1) * y ** 2 - 1
    bb = 2 * q * u * b
    pp = pair * index * transport
    expected = [(pp * (a + 1) - 1) ** 2 - d * (pp * bb) ** 2,
                pp * (a ** 2 - d * bb ** 2 + 1) - 1]
    for unit, target in zip((False, True), expected):
        body = candidate(parent, unit)
        values = dict(i=i, c2=c ** 2, aux_coefficient_root=delta * i * c ** 2,
                      R10a=c, T=t, r_lhs=r, norm_pair=pair,
                      norm_index=index, norm_transport=transport, R16=q, aux_y2=y ** 2)
        for name, op, left, right in body["source"][50:]:
            x = Poly(left) if type(left) is int else values[left]
            z = Poly(right) if type(right) is int else values[right]
            values[name] = x + z if op == "+" else x - z if op == "-" else x * z
        require(not (values[body["output"]] - target).terms, "complete literal tail polynomial identity")
    require(not (expected[0] - pp * expected[1] - (pp - 1) * (2 * pp * a - 1)).terms,
            "whole field/unit polynomial relation")
    # Independent generic auxiliary expansion in cut atoms (f,D,Q,u,b,R,y).
    f, dd, qq, uu, bc, rr, yy = map(Poly.atom, range(7))
    ef = f ** 2 - dd
    vv = uu * f - bc - rr * ef
    na = qq * vv ** 2 - (qq - 1) * yy ** 2
    ar = qq * (dd * uu ** 2 + bc ** 2) - (qq - 1) * yy ** 2 - 1
    br = 2 * qq * uu * bc
    qa = qq * (uu ** 2 - 2 * rr * uu * f + 2 * rr * bc + rr ** 2 * ef)
    require(not (na - 1 - ar + br * f - ef * qa).terms, "auxiliary root expansion")
    x, aa, cc, gg, hh = map(Poly.atom, range(5))
    require(not ((x + aa * cc + gg) ** 2 - (aa ** 2 + hh) * cc ** 2 -
                 (x ** 2 + 2 * aa * cc * x + 2 * gg * x + 2 * aa * cc * gg + gg ** 2 - hh * cc ** 2)).terms,
            "main-norm exact cancellation")
    require(all((a * a - dis * z * z) % 4 != 3 for a in range(4) for z in range(4) for dis in (0, 3)),
            "strong negative-unit exclusion")
    require(all((ss * ss * vv * vv + (1 - ss * ss) * yy * yy) % 4 != 3
                for ss in range(4) for vv in range(4) for yy in range(4)), "auxiliary negative-unit exclusion")
    return dict(status="PASS", exact_tail_normal_forms=2, auxiliary_expansion=True,
                field_unit_output_identity=True, main_norm_cancellation=True,
                strong_mod4_cases=32, auxiliary_mod4_cases=64,
                output_normal_form_monomials=[len(p.terms) for p in expected],
                scope="Exact sparse Z-polynomial identities at literal computed cuts, not sampled ring equalities.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    raw = PARENT.read_bytes()
    require(sha(raw) == PARENT_SHA, "pinned literal P67")
    parent = json.loads(raw)
    fixed, binding = fixed_values()
    files, receipt = {}, dict(status="PASS", scope="Literal topology/liveness and actual-coefficient degree checks. Ordinary proof separate; no Lean/frozen helper execution.",
                             coefficient_binding=binding, algebra=algebra_certificate(parent), circuits=[])
    for unit in (False, True):
        body = candidate(parent, unit)
        counts, degree = topology(body), degree_certificate(body, fixed)
        require(counts["operations"] == (75 if unit else 73), "complete operation count")
        name = "unit75" if unit else "field73"
        files[name + ".json"] = encode(body)
        files[name + "_degree.json"] = encode(degree)
        receipt["circuits"].append(dict(name=name, sha256=sha(files[name + ".json"]),
                                        degree=body["exact_degree"], **counts))
    files["CHECKS.json"] = encode(receipt)
    files["MANIFEST.json"] = encode({name: sha(value) for name, value in sorted(files.items())})
    for name, value in files.items():
        path = HERE / name
        if args.check:
            require(path.read_bytes() == value, "byte-identical rebuild: " + name)
        else:
            path.write_bytes(value)
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()

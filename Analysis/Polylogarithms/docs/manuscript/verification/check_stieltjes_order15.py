"""Verify the algebraic order-15 colored-tail point using exact arithmetic.

The input is a strict rational-polynomial certificate. Polynomial text is
parsed through a restricted arithmetic AST, never evaluated as Python.
Original-color Lerch numerators are rebuilt independently of the discovery
generator. No elimination, algebraic-root object, or numerical root solver
is used. All rejection checks remain active under python -O.
"""
from __future__ import annotations

import argparse
import ast
from copy import deepcopy
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import platform
import re
import sys
import time

import sympy as s

HERE = Path(__file__).resolve().parent
ORDER = 15
SCOPE = "Specified order-15 single-tail zero at a positive real shift and an upper nonalternating unit-circle color; A14 and A16 nonzero."
MAX_FILE_BYTES = 250000
MAX_INTEGER_BITS = 4096
a, w, b, t, X, Y = s.symbols("a w b t X Y", real=True)
POLYNOMIAL_KEYS = ("P", "N", "D", "R15", "I15")
INTERVAL_KEYS = ("Y_isolating_interval", "Y_enclosure", "X_enclosure", "D_enclosure")
ROOT_KEYS = ("schema_version", "order", "scope", *POLYNOMIAL_KEYS,
             *INTERVAL_KEYS, "adjacent_tails")


class VerificationError(ValueError):
    """Malformed evidence or a failed exact mathematical claim."""


def require(condition, message):
    if not bool(condition):
        raise VerificationError(message)


def exact_keys(record, keys, context):
    require(type(record) is dict and set(record) == set(keys),
            f"{context}: missing or unexpected fields")


def json_bytes(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=True).encode("ascii")


def digest(value):
    return hashlib.sha256(json_bytes(value)).hexdigest()


def text_digest(raw):
    return hashlib.sha256(raw.replace(b"\r\n", b"\n").replace(b"\r", b"\n")).hexdigest()


def load_json(raw):
    require(len(raw) <= MAX_FILE_BYTES, "Certificate exceeds size limit")

    def pairs_hook(pairs):
        out = {}
        for key, value in pairs:
            require(key not in out, f"Duplicate JSON field: {key}")
            out[key] = value
        return out

    def no_constant(value):
        raise VerificationError(f"Nonstandard JSON constant: {value}")

    try:
        return json.loads(raw, object_pairs_hook=pairs_hook,
                          parse_constant=no_constant)
    except (UnicodeError, json.JSONDecodeError) as exc:
        raise VerificationError(f"Invalid JSON: {exc}") from exc


@lru_cache(maxsize=48)
def rational_polynomial(text, variables, max_degree=64):
    """Parse into QQ[variables], bounding degree before polynomial products."""
    require(type(text) is str and 0 < len(text) <= 50000,
            "Polynomial must be a bounded nonempty string")
    names = {str(v): s.Poly(v, *variables, domain=s.QQ) for v in variables}

    def bounded(poly):
        require(poly.total_degree() <= max_degree, "Polynomial degree limit exceeded")
        require(len(poly.terms()) <= 2500, "Polynomial term limit exceeded")
        require(all(abs(int(c.p)).bit_length() <= MAX_INTEGER_BITS
                    and int(c.q).bit_length() <= MAX_INTEGER_BITS
                    for c in poly.coeffs()), "Polynomial coefficient size limit exceeded")
        return poly

    def parse(node, depth=0):
        require(depth <= 160, "Polynomial syntax nesting limit exceeded")
        if isinstance(node, ast.Constant) and type(node.value) is int:
            require(abs(node.value).bit_length() <= MAX_INTEGER_BITS,
                    "Integer size limit exceeded")
            return s.Poly(node.value, *variables, domain=s.QQ)
        if isinstance(node, ast.Name) and node.id in names:
            return names[node.id]
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
            operand = parse(node.operand, depth + 1)
            return operand if isinstance(node.op, ast.UAdd) else -operand
        if isinstance(node, ast.BinOp):
            left, right = parse(node.left, depth + 1), parse(node.right, depth + 1)
            if isinstance(node.op, ast.Add):
                return bounded(left + right)
            if isinstance(node.op, ast.Sub):
                return bounded(left - right)
            if isinstance(node.op, ast.Mult):
                require(left.total_degree() + right.total_degree() <= max_degree,
                        "Polynomial degree limit exceeded")
                return bounded(left * right)
            if isinstance(node.op, ast.Div):
                require(right.total_degree() == 0 and not right.is_zero,
                        "Only nonzero rational scalar divisors are allowed")
                return bounded(left.mul_ground(1 / right.LC()))
            if isinstance(node.op, ast.Pow):
                require(right.total_degree() == 0 and right.LC().q == 1
                        and 0 <= right.LC() <= 64,
                        "Polynomial exponent must be an integer in 0..64")
                exponent = int(right.LC())
                require(left.total_degree() * exponent <= max_degree,
                        "Polynomial degree limit exceeded")
                return bounded(left ** exponent)
        raise VerificationError("Unsupported polynomial syntax or undeclared variable")

    try:
        tree = ast.parse(text, mode="eval")
        require(sum(1 for _ in ast.walk(tree)) <= 5000,
                "Polynomial syntax node limit exceeded")
        return bounded(parse(tree.body))
    except VerificationError:
        raise
    except (SyntaxError, ValueError, TypeError, RecursionError,
            s.PolynomialError) as exc:
        raise VerificationError(f"Invalid rational polynomial: {exc}") from exc


def rational(text):
    require(type(text) is str and len(text) <= 2600
            and re.fullmatch(r"[+-]?[0-9]+(?:/[1-9][0-9]*)?", text) is not None,
            "Interval endpoint must be an exact integer or rational string")
    parts = text.split("/")
    numerator, denominator = int(parts[0]), int(parts[1]) if len(parts) == 2 else 1
    require(abs(numerator).bit_length() <= MAX_INTEGER_BITS
            and denominator.bit_length() <= MAX_INTEGER_BITS,
            "Interval endpoint size limit exceeded")
    return s.Rational(numerator, denominator)


def read_interval(value, context):
    require(type(value) is list and len(value) == 2,
            f"{context}: expected exactly two interval endpoints")
    result = tuple(rational(c) for c in value)
    require(result[0] <= result[1], f"{context}: reversed interval")
    return result


def add(U, V):
    return U[0] + V[0], U[1] + V[1]


def mul(U, V):
    products = [u * v for u in U for v in V]
    return min(products), max(products)


def reciprocal(U):
    require(U[0] * U[1] > 0, "Reciprocal interval contains zero")
    return min(1 / U[0], 1 / U[1]), max(1 / U[0], 1 / U[1])


def evaluate(poly, interval):
    result = (s.Rational(0), s.Rational(0))
    for coefficient in poly.all_coeffs():
        result = add(mul(result, interval), (coefficient, coefficient))
    return result


def contains(outer, inner):
    return outer[0] <= inner[0] <= inner[1] <= outer[1]


def primitive(poly):
    return poly.clear_denoms()[1].primitive()[1]


def normalized_polynomial(poly):
    return {"variables": [str(v) for v in poly.gens],
            "terms": [{"powers": list(powers), "coefficient": str(coefficient)}
                      for powers, coefficient in poly.terms()]}


@lru_cache(maxsize=1)
def independent_tails():
    """Reconstruct once, from the original (omega,a) numerator recurrence."""
    num = s.Integer(1)
    R, I, checks = {}, {}, []
    for k in range(17):
        if k >= 14:
            pc = s.Poly(num, w)
            require(pc.degree() <= k, "Original numerator degree invariant")
            normalized = s.expand(sum(
                pc.nth(j).subs(a, b + s.Rational(1, 2))
                * (s.I*t - 1)**j * (s.I*t + 1)**(k-j)
                for j in range(k+1)) / 2**k)
            real = s.Poly(s.expand(s.re(normalized) / (b if k % 2 else 1)), b, t)
            imag = s.Poly(s.expand(s.im(normalized) / (t * (b if k % 2 == 0 else 1))), b, t)
            for label, polynomial, destination in (("R", real, R), ("I", imag, I)):
                name = f"Original-color parity of {label}{k}"
                require(all(i % 2 == j % 2 == 0 for (i, j), _ in polynomial.terms()), name)
                destination[k] = s.Poly(sum(c * X**(i//2) * Y**(j//2)
                    for (i, j), c in polynomial.terms()), X, Y, domain=s.QQ)
                checks.append(name)
            rebuilt = ((b if k % 2 else 1) * R[k].as_expr()
                       + s.I*t*(b if k % 2 == 0 else 1)*I[k].as_expr()).subs({X: b*b, Y: t*t})
            name = f"Original-color normalization at order {k}"
            require(s.expand(normalized-rebuilt) == 0, name)
            checks.append(name)
        if k < 16:
            num = s.expand(w*(1-w)*s.diff(num, w) + (a+(k+1-a)*w)*num)
    return R, I, tuple(checks)


@lru_cache(maxsize=8)
def modular_tail_checks(P, N, D):
    """Reuse residues across corruptions that do not alter the rational lift."""
    R, I, _ = independent_tails()
    ns = [s.Poly(1, Y, domain=s.QQ)]
    ds = ns.copy()
    for _ in range(7):
        ns.append((ns[-1]*N).rem(P))
        ds.append((ds[-1]*D).rem(P))
    results = []
    for poly in (R[15], I[15]):
        px = s.Poly(poly.as_expr(), X)
        require(px.degree() == 7, "Order-15 homogenization degree must be seven")
        residue = s.Poly(0, Y, domain=s.QQ)
        for j in range(8):
            coefficient = s.Poly(px.nth(j), Y, domain=s.QQ)
            residue = (residue + coefficient*ns[j]*ds[7-j]).rem(P)
        results.append(residue.is_zero)
    return tuple(results)


def verify_payload(data):
    exact_keys(data, ROOT_KEYS, "certificate")
    require(type(data["schema_version"]) is int and data["schema_version"] == 1,
            "Unsupported schema version")
    require(type(data["order"]) is int and data["order"] == ORDER,
            "Certificate order must be exactly 15")
    require(data["scope"] == SCOPE, "Unexpected declared scope")
    polys = {key: rational_polynomial(data[key], (X, Y) if key in ("R15", "I15") else (Y,))
             for key in POLYNOMIAL_KEYS}
    intervals = {key: read_interval(data[key], key) for key in INTERVAL_KEYS}
    exact_keys(data["adjacent_tails"], ("14", "16"), "adjacent tails")
    adjacent = {}
    for k in ("14", "16"):
        exact_keys(data["adjacent_tails"][k], ("R_interval", "I_interval"), f"tail {k}")
        adjacent[k] = {key: read_interval(value, f"tail {k} {key}")
                       for key, value in data["adjacent_tails"][k].items()}
    checks = []

    def check(name, condition):
        require(condition, name)
        checks.append({"name": name, "pass": True})

    P, N, D = (polys[key] for key in ("P", "N", "D"))
    check("P has primitive integer coefficients", P.clear_denoms()[0] == 1 and abs(P.primitive()[0]) == 1)
    check("P has degree 42", P.degree() == 42)
    check("N has degree 37", N.degree() == 37)
    check("D has degree 36", D.degree() == 36)
    check("P has positive leading and negative constant coefficients", P.LC() > 0 and P.TC() < 0)
    signs = [s.sign(c) for c in P.all_coeffs() if c]
    check("P has exactly one Descartes sign variation", sum(x != y for x, y in zip(signs, signs[1:])) == 1)
    check("P coefficients are negative in degrees 0..31 and positive in degrees 32..42",
          all(P.nth(k) < 0 for k in range(32)) and all(P.nth(k) > 0 for k in range(32, 43)))
    check("P signs bracket a root in (1,2)", P.eval(1) < 0 < P.eval(2))
    yint, ybox, xbox = (intervals[key] for key in ("Y_isolating_interval", "Y_enclosure", "X_enclosure"))
    check("Rational endpoints isolate the unique positive root", 1 < yint[0] < yint[1] < 2
          and P.eval(yint[0]) < 0 < P.eval(yint[1]))
    check("Displayed Y box contains the isolating interval", contains(ybox, yint))
    dint = evaluate(D, yint)
    check("Lift denominator excludes zero", dint[0]*dint[1] > 0)
    check("Stored denominator enclosure is sound", contains(intervals["D_enclosure"], dint))
    xint = mul(evaluate(N, yint), reciprocal(dint))
    check("Displayed X box contains the rational lift", contains(xbox, xint))
    check("Positive shift and nonalternating Cayley domain", xbox[0] > s.Rational(1, 4) and ybox[0] > 0)
    R, I, independent_checks = independent_tails()
    checks.extend({"name": name, "pass": True} for name in independent_checks)
    check("Supplied primitive R15 equals the independently rebuilt polynomial", polys["R15"] == primitive(R[15]))
    check("Supplied primitive I15 equals the independently rebuilt polynomial", polys["I15"] == primitive(I[15]))
    check("R15 has X degree seven for denominator clearing", R[15].degree(X) == 7)
    check("I15 has X degree seven for denominator clearing", I[15].degree(X) == 7)
    rzero, izero = modular_tail_checks(P, N, D)
    check("D^7 R15(N/D,Y) vanishes modulo P", rzero)
    check("D^7 I15(N/D,Y) vanishes modulo P", izero)

    def evaluate_xy(poly):
        result = (s.Rational(0), s.Rational(0))
        for coefficient in s.Poly(poly.as_expr(), X).all_coeffs():
            result = add(mul(result, xbox), evaluate(s.Poly(coefficient, Y), ybox))
        return result

    for k in (14, 16):
        rint, iint = evaluate_xy(R[k]), evaluate_xy(I[k])
        check(f"A{k} is nonzero throughout the rational box", rint[0]*rint[1] > 0 or iint[0]*iint[1] > 0)
        check(f"Stored R{k} enclosure is sound", contains(adjacent[str(k)]["R_interval"], rint))
        check(f"Stored I{k} enclosure is sound", contains(adjacent[str(k)]["I_interval"], iint))
    require(len(checks) == 35, "Unexpected exact-check count")
    normalized = {"schema_version": 1, "order": ORDER, "scope": SCOPE,
                  "polynomials": {key: normalized_polynomial(poly) for key, poly in polys.items()},
                  "intervals": {key: list(map(str, value)) for key, value in intervals.items()},
                  "adjacent_tails": {k: {key: list(map(str, value)) for key, value in row.items()}
                                     for k, row in adjacent.items()}}
    metadata = {"polynomial_degrees": {key: int(poly.total_degree()) for key, poly in polys.items()},
                "normalized_polynomial_sha256": {key: digest(normalized_polynomial(poly)) for key, poly in polys.items()},
                "normalized_certificate_sha256": digest(normalized)}
    return checks, metadata


def negative_controls(data):
    controls = []

    def corrupt(name, mutate, expected):
        candidate = deepcopy(data)
        mutate(candidate)
        try:
            verify_payload(candidate)
        except VerificationError as exc:
            require(expected in str(exc), f"Wrong rejection for {name}: {exc}")
            controls.append({"name": name, "rejected": True, "reason": str(exc)})
            return
        raise VerificationError(f"Corrupted certificate was accepted: {name}")

    corrupt("Wrong order label", lambda d: d.__setitem__("order", 14), "order must be exactly")
    corrupt("Boolean masquerading as an order", lambda d: d.__setitem__("order", True), "order must be exactly")
    corrupt("Missing adjacent order 16", lambda d: d["adjacent_tails"].pop("16"), "missing or unexpected")
    corrupt("Extra ignored interval endpoint", lambda d: d["Y_enclosure"].append("2"), "exactly two")
    corrupt("Reversed isolating endpoints", lambda d: d["Y_isolating_interval"].reverse(), "reversed interval")
    corrupt("Floating interval endpoint", lambda d: d["Y_enclosure"].__setitem__(0, "1.8"), "exact integer or rational")
    corrupt("False lifted X enclosure", lambda d: d.__setitem__("X_enclosure", ["1", "2"]), "contains the rational lift")
    midpoint = sum(map(rational, data["Y_isolating_interval"])) / 2
    corrupt("Denominator with a zero inside the isolating interval", lambda d: d.__setitem__("D", f"Y**35*(Y-({midpoint}))"), "denominator excludes zero")
    corrupt("Alter primitive tail polynomial", lambda d: d.__setitem__("R15", f"({d['R15']})+1"), "Supplied primitive R15")
    corrupt("Alter lift numerator coefficient", lambda d: d.__setitem__("N", f"({d['N']})+1"), "R15(N/D,Y) vanishes")
    def alter_denominator(d):
        d["D"] = f"({d['D']})+1"
        d["D_enclosure"] = [str(rational(endpoint)+1) for endpoint in d["D_enclosure"]]
    corrupt("Alter lift denominator coefficient with matching enclosure", alter_denominator, "R15(N/D,Y) vanishes")
    corrupt("Reverse P orientation", lambda d: d.__setitem__("P", f"-({d['P']})"), "positive leading")
    corrupt("Wrong degree for P", lambda d: d.__setitem__("P", f"({d['P']})+Y**43"), "degree 42")
    corrupt("False adjacent-tail enclosure", lambda d: d["adjacent_tails"]["14"].__setitem__("R_interval", ["0", "1"]), "Stored R14 enclosure")
    corrupt("Function-call expression", lambda d: d.__setitem__("P", "sin(Y)"), "Unsupported polynomial syntax")
    corrupt("Attribute-access expression", lambda d: d.__setitem__("P", "(1).__class__"), "Unsupported polynomial syntax")
    corrupt("Undeclared polynomial variable", lambda d: d.__setitem__("P", "X+Y"), "Unsupported polynomial syntax")
    corrupt("Unexpected unverified certificate field", lambda d: d.__setitem__("accepted", True), "missing or unexpected")
    for name, raw in (("Duplicate JSON field", b'{"order":15,"order":14}'),
                      ("Nonstandard NaN JSON number", b'{"order":NaN}')):
        try:
            load_json(raw)
        except VerificationError as exc:
            controls.append({"name": name, "rejected": True, "reason": str(exc)})
        else:
            raise VerificationError(f"Malformed JSON was accepted: {name}")
    require(len(controls) == 20, "Unexpected corruption-control count")
    return controls


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path, default=HERE/"stieltjes-order15-certificate.json")
    parser.add_argument("--output", type=Path, default=HERE/"stieltjes-order15-verification.json")
    args = parser.parse_args()
    started = time.monotonic()
    metadata = {"schema_version": 1, "status": "RUNNING", "order": ORDER,
                "scope": SCOPE, "python": platform.python_version(), "sympy": s.__version__,
                "python_optimization_level": sys.flags.optimize,
                "certificate_file": args.certificate.name,
                "digest_mode": "SHA-256 after replacing CRLF and CR by LF; other bytes unchanged",
                "verifier_sha256": text_digest(Path(__file__).read_bytes())}

    def write_receipt(value):
        args.output.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")

    try:
        require(args.certificate.resolve() != args.output.resolve()
                and not (args.certificate.exists() and args.output.exists()
                         and args.certificate.samefile(args.output)),
                "Input certificate and output receipt must be distinct files")
    except VerificationError as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1
    try:
        write_receipt(metadata)
        raw = args.certificate.read_bytes()
        metadata["certificate_sha256"] = text_digest(raw)
        data = load_json(raw)
        checks, polynomial_metadata = verify_payload(data)
        print(f"PASS: {len(checks)} base exact checks; testing corruptions", flush=True)
        controls = negative_controls(data)
        result = {**metadata, **polynomial_metadata, "status": "PASS",
                  "exact_check_count": len(checks), "corruption_control_count": len(controls),
                  "checks": checks, "corruption_controls": controls,
                  "elapsed_seconds": round(time.monotonic()-started, 3),
                  "method": "Independent original-color recurrence, restricted rational-polynomial parsing, Descartes signs, modular lift identities and rational interval bounds.",
                  "limitations": "Certifies the specified order-15 point and its conjugate, not a complete order-15 locus, minimal algebraic degree, or consecutive-tail counterexample."}
        write_receipt(result)
        print(f"PASS: {len(checks)} exact checks, {len(controls)} rejected corruptions", flush=True)
        return 0
    except Exception as exc:
        failure = {**metadata, "status": "FAIL", "error": f"{type(exc).__name__}: {exc}",
                   "elapsed_seconds": round(time.monotonic()-started, 3)}
        try:
            write_receipt(failure)
        except OSError as output_error:
            print(f"Cannot write failure receipt: {output_error}", file=sys.stderr)
        print(f"FAIL: {failure['error']}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())

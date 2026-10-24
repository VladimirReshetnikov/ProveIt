#!/usr/bin/env python3
"""Independent finite audit of the supplied shared-CRT quartic.

Finite controls are implementation checks, not a proof of Con(ZFC), and
not a substitute for the universal mathematical argument in the article.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from hashlib import sha256
import importlib.util
import json
import sys
from math import comb, factorial, gcd, prod
from pathlib import Path


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def pell(a, n):
    """Independent binary powering in Z[sqrt(a*a-1)]."""
    d = a * a - 1
    x, y, u, v = 1, 0, a, 1
    while n:
        if n & 1:
            x, y = x * u + d * y * v, x * v + y * u
        u, v = u * u + d * v * v, 2 * u * v
        n //= 2
    return x, y


def positive_power_values(n, k):
    require(n > 0 and k > 0, "positive case required")
    W = n + k
    j = 1
    while True:
        A, wz = pell(W + 1, j)
        T = 2 * A * n - n * n - 1
        if wz % W == 0 and T > n**k:
            break
        j += 1
        require(j <= 1000, "fixture search bound")
    X, Y = pell(A, k)
    U, V = pell(A, 2 * k * Y)
    require(V % (Y * Y) == 0 and V > 0, "Pell divisor fixture")
    require(gcd(U, 4 * Y) == 1, "Pell CRT fixture")
    # B congruent A modulo U and 1 modulo 4Y; take a positive representative.
    B = A + U * (((1 - A) * pow(U, -1, 4 * Y)) % (4 * Y))
    if B < 2:
        B += U * 4 * Y
    S, R = pell(B, k)
    return dict(W=W, A=A, T=T, Z=wz // W, X=X, Y=Y,
                U=U, V=V, S=S, R=R, B=B)


def assign_congruence(assignments, name, left, right, modulus):
    require(modulus > 0 and (right - left) % modulus == 0,
            "fixture congruence is not exact")
    q = (right - left) // modulus
    assignments[name + ".qp.1"] = max(q, 0)
    assignments[name + ".qm.1"] = max(-q, 0)


def evaluate_builder(builder, assignments, powers=None):
    """Solve only definitional arithmetic gates, then independently check rows."""
    vals = []
    powers = powers or {}
    for i, variable in enumerate(builder.variables):
        if i in powers:
            a, b = powers[i]
            def atom(t):
                return t[1] if t[0] == "c" else vals[t[1]]
            value = atom(a) ** atom(b)
        elif i in builder.gates:
            row = builder.rows[builder.gates[i]]
            coefficient = 0
            rest = 0
            for c, mon in row["terms"]:
                if mon == [i]:
                    coefficient += c
                else:
                    require(i not in mon and all(j < i for j in mon),
                            "non-topological arithmetic gate")
                    rest += c * prod(vals[j] for j in mon)
            require(coefficient == 1, "gate output coefficient")
            value = -rest
        else:
            value = assignments.get(variable["name"], 0)
        require(value >= 0, "non-natural fixture value")
        vals.append(value)
    residuals = [sum(c * prod(vals[j] for j in mon)
                     for c, mon in row["terms"]) for row in builder.rows]
    return vals, residuals


def power_checks(module):
    cases = []
    for n in range(5):
        cases.append((n, 0))
    for k in range(1, 6):
        cases.append((0, k))
    cases += [(1, 1), (2, 1), (1, 2), (2, 2)]  # Keep complete finite witnesses modest.
    case_counts = defaultdict(int)
    for n, k in cases:
        b = module.Builder()
        an, ak = b.new("test.n"), b.new("test.k")
        out = b.power(an, ak)
        names = {v["name"] for v in b.variables}
        assignment = {"test.n": n, "test.k": k, "pow0.output": n**k}
        if k == 0:
            assignment["pow0.case0"] = 1
            case_counts["exponent_zero"] += 1
        elif n == 0:
            assignment.update({"pow0.case1": 1, "pow0.kminus1": k - 1})
            case_counts["base_zero"] += 1
        else:
            z = positive_power_values(n, k)
            assignment.update({"pow0.case2": 1, "pow0.kminus1": k - 1,
                               "pow0.nminus1": n - 1})
            for key in ("A", "T", "Z", "X", "Y"):
                assignment["pow0." + key] = z[key]
            for key in ("U", "V", "S", "R", "B"):
                assignment["pow0.pell." + key] = z[key]
            assignment.update({
                "pow0.slack.yk": z["Y"] - k,
                "pow0.q4": (z["B"] - 1) // (4 * z["Y"]),
                "pow0.Vquotient_minus1": z["V"] // z["Y"]**2 - 1,
                "pow0.slack.gap": z["T"] - n**k - 1,
            })
            for name, left, right, modulus in (
                ("B_mod_U", z["B"], z["A"], z["U"]),
                ("S_mod_U", z["S"], z["X"], z["U"]),
                ("R_mod_4Y", z["R"], k, 4 * z["Y"]),
                ("power_congruence", z["X"] + z["Y"] * n,
                 z["Y"] * z["A"] + n**k, z["T"]),
            ):
                assign_congruence(assignment, "pow0." + name, left, right, modulus)
            require(z["A"] > z["W"] >= n,
                    "integer subtraction justification fixture")
            case_counts["positive"] += 1
        require(set(assignment) <= names, "unrecognized fixture assignment")
        values, residuals = evaluate_builder(b, assignment)
        require(not any(residuals), f"power fixture failed at {n}^{k}")
        if n > 0 and k > 0:
            specialized = module.Builder(positive_powers=True)
            sn, sk = specialized.new("test.n"), specialized.new("test.k")
            specialized.power(sn, sk)
            snames = {v["name"] for v in specialized.variables}
            selected_assignment = {key: val for key, val in assignment.items() if key in snames}
            require(not any(evaluate_builder(specialized, selected_assignment)[1]),
                    "positive-specialized power fixture")
            selected_assignment["pow0.output"] += 1
            require(any(evaluate_builder(specialized, selected_assignment)[1]),
                    "mutated positive-specialized power escaped")
            case_counts["positive_specialized"] += 1
        assignment["pow0.output"] += 1
        _, bad = evaluate_builder(b, assignment)
        require(any(bad), "mutated power output escaped rows")
        require(values[out[1]] == n**k, "wrong power output")
    return dict(case_counts) | {"mutated_outputs_rejected": len(cases)}


def positive_call_induction(module, directory):
    source = json.loads((directory / "wire_eliminated_source.json").read_text())
    builder = module.construct(source, "mixed13", positive_powers=True)
    arithmetic = {out: key for key, out in builder.cache.items()}
    proved_lower = {}
    checked = 0
    for macro in builder.macro_log:
        memo = {}
        def lower(atom):
            if atom[0] == "c":
                return atom[1]
            if atom in proved_lower:
                return proved_lower[atom]
            if atom in memo:
                return memo[atom]
            if atom not in arithmetic:
                return 0
            op, a, b = arithmetic[atom]
            left, right = lower(a), lower(b)
            value = left + right if op == "add" else left * right
            # Only positivity is needed; cap lower bounds to avoid huge values.
            memo[atom] = min(value, 2)
            return memo[atom]
        if macro["macro"] == "power":
            require(lower(macro["base"]) >= 1, "power base lacks positivity proof")
            require(lower(macro["exponent"]) >= 1,
                    "power exponent lacks positivity proof")
            proved_lower[macro["output"]] = 1
            checked += 1
        elif macro["macro"] == "factorial":
            require(lower(macro["n"]) >= 1,
                    "specialized factorial argument lacks positivity proof")
            # Its power and binomial prerequisites occur earlier in macro_log.
            proved_lower[macro["output"]] = 1
        elif macro["macro"] == "binomial":
            require(lower(macro["n"]) >= 1 and lower(macro["k"]) >= 1,
                    "specialized binomial argument lacks positivity proof")
        else:
            raise AssertionError("unknown macro in positivity induction")
    require(checked == len(builder.powers), "not every power call audited")
    return dict(positive_power_calls=checked,
                method="Induction through prior macro outputs and nonnegative arithmetic gates")


def elementary_macro_checks(module):
    # Powers are replaced by exact arithmetic only in these isolated controls;
    # the actual Pell power graph is tested separately above.
    class ExactPowerBuilder(module.Builder):
        def __init__(self):
            super().__init__()
            self.exact_powers = {}

        def power(self, n, k):
            key = (n, k)
            if key not in self.powers:
                out = self.new(f"exact_power.{len(self.powers)}")
                self.powers[key] = out
                self.exact_powers[out[1]] = key
            return self.powers[key]

    binomial_cases = 0
    for n in range(7):
        for k in range(9):
            b = ExactPowerBuilder()
            an, ak = b.new("n"), b.new("k")
            b.binomial(an, ak)
            q = 2**n + 1
            numerator, denominator = (q + 1)**n, q**k
            quotient, remainder = divmod(numerator, denominator)
            output = comb(n, k) if k <= n else 0
            assignment = {"n": n, "k": k, "choose0.output": output,
                          "choose0.high": quotient // q,
                          "choose0.remainder": remainder,
                          "choose0.rslack": denominator - remainder - 1,
                          "choose0.oslack": q - output - 1}
            _, rs = evaluate_builder(b, assignment, b.exact_powers)
            require(not any(rs), "binomial macro fixture")
            assignment["choose0.output"] += 1
            require(any(evaluate_builder(b, assignment, b.exact_powers)[1]),
                    "mutated binomial output escaped")
            binomial_cases += 1
    # Independent arithmetic formula checks, including n=0 and n=1.
    factorial_cases = 0
    for n in range(20):
        radius = (n + 2)**(n + 2)
        c = comb(radius + n, n)
        numerator = (radius + 1)**n
        require((numerator + c - 1) // c == factorial(n),
                "factorial ceiling identity")
        factorial_cases += 1
    product_cases = 0
    for n in range(5):
        for t in range(1, 7):
            q = (1 + (n + 1) * t)**n + 2
            expected = prod(1 + (i + 1) * t for i in range(n))
            require((t**n * factorial(n) * comb(q + n, n)) % (t * q - 1) == expected,
                    "CRT modulus product identity")
            product_cases += 1
    return dict(binomial_macros=binomial_cases,
                mutated_binomial_outputs_rejected=binomial_cases,
                factorial_ceiling_identities=factorial_cases,
                modulus_product_identities=product_cases)


def finite_crt_checks():
    # Test the actual bounded source E(i,w)=w,F(i,w)=i for three rows.
    N, U = 3, 2
    H = U + N + N + U + 1
    T = factorial(H)
    moduli = [1 + (i + 1) * T for i in range(N)]
    B = prod(moduli)
    require(all(gcd(a, b) == 1 for i, a in enumerate(moduli)
                for b in moduli[:i]), "CRT fixture moduli")
    def crt(residues):
        x, modulus = 0, 1
        for r, d in zip(residues, moduli):
            x += modulus * (((r - x) * pow(modulus, -1, d)) % d)
            modulus *= d
        return x
    A = C = crt(range(N))
    require(comb(A, U + 1) % B == 0, "factorial-free binomial bound")
    require((1 + (C + 1) * T) % B == 0, "CRT encoded index")
    require((A - C) % B == 0, "CRT source equation")
    # The composite residue must not be used in the soundness proof.
    require(prod(16 - i for i in range(3)) % 35 == 0 and not 0 <= 16 % 35 <= 2,
            "composite-root negative control")
    return dict(rows=N, factorial_bound=H,
                factorial_free_divisibility=True,
                composite_residue_negative_control=True)


def polynomial_check(directory):
    eqpath = directory / "equation.json"
    polypath = directory / "expanded_polynomial.json"
    eq = json.loads(eqpath.read_text())
    poly = json.loads(polypath.read_text())
    n = len(eq["variables"])
    require(eq["domain"] == "nonnegative integers", "equation domain")
    require(len({v["name"] for v in eq["variables"]}) == n, "duplicate variable names")
    expanded = defaultdict(int)
    used = set()
    for row in eq["residuals"]:
        require(row["terms"], "empty residual")
        previous = set()
        for c, mon in row["terms"]:
            require(isinstance(c, int) and c != 0, "invalid row coefficient")
            require(len(mon) <= 2 and mon == sorted(mon), "nonquadratic row")
            require(all(isinstance(j, int) and 0 <= j < n for j in mon), "variable range")
            require(tuple(mon) not in previous, "repeated row monomial")
            previous.add(tuple(mon))
            used.update(mon)
        for a, ma in row["terms"]:
            for b, mb in row["terms"]:
                expanded[tuple(sorted(ma + mb))] += a * b
    expected = {mon: c for mon, c in expanded.items() if c}
    delivered = {tuple(mon): c for c, mon in poly["terms"]}
    require(len(delivered) == len(poly["terms"]), "duplicate expanded monomial")
    require(expected == delivered, "expanded polynomial differs from SOS")
    require(used == set(range(n)), "unused quantified variable")
    require(poly["variables"] == n, "polynomial variable count")
    require(max(map(len, expected)) == 4, "exact degree is not four")
    return dict(variables=n, rows=len(eq["residuals"]),
                expanded_monomials=len(expected), exact_degree=4,
                max_abs_coefficient=max(map(abs, expected.values())),
                equation_sha256=sha256(eqpath.read_bytes()).hexdigest(),
                expanded_sha256=sha256(polypath.read_bytes()).hexdigest())


def affine_restoration_check(module, directory, equation_directory=None):
    """Infer the restoration from old rows and final variable names, not export code."""
    source = json.loads((directory / "wire_eliminated_source.json").read_text())
    builder = module.construct(source, "mixed13", positive_powers=True)
    equation_directory = equation_directory or directory
    equation = json.loads((equation_directory / "equation.json").read_text())
    retained = {v["name"]: i for i, v in enumerate(equation["variables"])}
    expressions = {}
    eliminated = []

    def add(target, value, scale=1):
        for mon, coefficient in value.items():
            target[mon] += coefficient * scale

    def multiply(a, b):
        result = defaultdict(int)
        for ma, ca in a.items():
            for mb, cb in b.items():
                result[tuple(sorted(ma + mb))] += ca * cb
        return {mon: c for mon, c in result.items() if c}

    def substitute(terms):
        result = defaultdict(int)
        for coefficient, monomial in terms:
            value = {(): coefficient}
            for original in monomial:
                require(original in expressions, "restoration depends on a future variable")
                value = multiply(value, expressions[original])
            add(result, value)
        return {mon: c for mon, c in result.items() if c}

    for original, variable in enumerate(builder.variables):
        name = variable["name"]
        if name in retained:
            expressions[original] = {(retained[name],): 1}
            continue
        require(original in builder.gates, "a non-gate witness disappeared")
        row = builder.rows[builder.gates[original]]
        output_coefficient = sum(c for c, mon in row["terms"] if mon == [original])
        require(output_coefficient == 1, "restoration is not monic")
        rest = [(c, mon) for c, mon in row["terms"] if mon != [original]]
        require(all(original not in mon for _, mon in rest), "recursive restoration")
        restored = {mon: -c for mon, c in substitute(rest).items()}
        require(all(c >= 0 and len(mon) <= 1 for mon, c in restored.items()),
                "removed gate does not have nonnegative affine restoration")
        expressions[original] = restored
        eliminated.append(original)

    original_rows = Counter()
    for row in builder.rows:
        transformed = substitute(row["terms"])
        if transformed:
            require(max(map(len, transformed)) <= 2, "restored row exceeds quadratic degree")
            original_rows[tuple(sorted(transformed.items()))] += 1
    delivered_rows = Counter(tuple(sorted((tuple(mon), c) for c, mon in row["terms"]))
                             for row in equation["residuals"])
    require(original_rows == delivered_rows,
            "remaining rows differ from independently restored original rows")
    return dict(original_variables=len(builder.variables),
                remaining_variables=len(retained),
                eliminated_affine_gates=len(eliminated),
                restored_rows=len(builder.rows),
                remaining_rows=len(equation["residuals"]),
                maximum_affine_support=max((len(expressions[i]) for i in eliminated), default=0),
                exact_row_multiset_identity=True,
                natural_witness_restoration=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--directory", type=Path, required=True)
    ap.add_argument("--equation-directory", type=Path,
                    help="optional location of a companion equation, using the same source builder")
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    build = args.directory / "build_equation.py"
    sys.path.insert(0, str(args.directory.resolve()))
    spec = importlib.util.spec_from_file_location("reviewed_builder", build)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    equation_directory = args.equation_directory or args.directory
    result = dict(status="PASS", optimized=not __debug__,
                  source_builder_sha256=sha256(build.read_bytes()).hexdigest(),
                  scope="Independent finite controls; no Lean build and no Con(ZFC) decision.",
                  polynomial=polynomial_check(equation_directory),
                  affine_restoration=affine_restoration_check(module, args.directory, equation_directory),
                  power=power_checks(module),
                  positivity=positive_call_induction(module, args.directory),
                  elementary_macros=elementary_macro_checks(module),
                  crt=finite_crt_checks())
    calculus_path = args.directory / "direct_calculus.py"
    if calculus_path.exists():
        result["source_calculus_sha256"] = sha256(calculus_path.read_bytes()).hexdigest()
    result["checker_sha256"] = sha256(Path(__file__).read_bytes()).hexdigest()
    encoded = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(encoded)
    print(encoded, end="")


if __name__ == "__main__":
    main()

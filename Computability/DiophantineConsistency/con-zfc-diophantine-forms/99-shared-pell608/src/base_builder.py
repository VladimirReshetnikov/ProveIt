#!/usr/bin/env python3
"""Materialize an ordinary quartic from a fixed numerical Horn-rule source.

All quantified variables are nonnegative integers. The final equation is the
sum of the squares of the quadratic residuals in equation.json. Arithmetic
macros below expand into these residuals; no power, factorial, binomial,
division, or bounded-quantifier operator remains in that equation.

This is new research code, not a Lean proof. See the report for mathematical
dependencies, including the inherited numerical-calculus calibration.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from hashlib import sha256
import json
from pathlib import Path
from direct_calculus import source_pair_calculus


def require(ok, message):
    if not ok:
        raise ValueError(message)


def const(n):
    require(isinstance(n, int) and n >= 0, "natural constant required")
    return ("c", n)


ZERO, ONE, TWO, FOUR = map(const, (0, 1, 2, 4))


class Builder:
    def __init__(self, positive_powers=False):
        self.positive_powers = positive_powers
        self.variables = []
        self.rows = []
        self.gates = {}
        self.cache = {}
        self.powers = {}
        self.binomials = {}
        self.factorials = {}
        self.macro_log = []
        self.counter = Counter()
        self.shared_digit_limit = None
        self.shared_digit_base = None

    def new(self, name, kind="witness"):
        i = len(self.variables)
        self.variables.append({"name": name, "kind": kind})
        return ("v", i)

    def fresh(self, prefix):
        self.counter[prefix] += 1
        return self.new(f"{prefix}.{self.counter[prefix]}")

    def row(self, terms, label, gate=None):
        coefficients = defaultdict(int)
        for coefficient, atoms in terms:
            indices = []
            for atom in atoms:
                if atom[0] == "c":
                    coefficient *= atom[1]
                else:
                    indices.append(atom[1])
            coefficients[tuple(sorted(indices))] += coefficient
        sparse = [[c, list(m)] for m, c in sorted(coefficients.items()) if c]
        require(all(len(m) <= 2 for c, m in sparse), "nonquadratic row")
        if not sparse:
            return
        index = len(self.rows)
        self.rows.append({"label": label, "terms": sparse, "gate": gate})
        if gate is not None:
            self.gates[gate] = index

    def eq(self, left, right, label, guard=None):
        prefix = [] if guard is None else [guard]
        self.row([(1, prefix + [left]), (-1, prefix + [right])], label)

    def add(self, a, b):
        if a == ZERO:
            return b
        if b == ZERO:
            return a
        if a[0] == b[0] == "c":
            return const(a[1] + b[1])
        a, b = sorted((a, b))
        key = ("add", a, b)
        if key not in self.cache:
            out = self.new(f"add.{len(self.cache)}", "gate")
            self.cache[key] = out
            self.row([(1, [out]), (-1, [a]), (-1, [b])], "addition", out[1])
        return self.cache[key]

    def mul(self, a, b):
        if ZERO in (a, b):
            return ZERO
        if a == ONE:
            return b
        if b == ONE:
            return a
        if a[0] == b[0] == "c":
            return const(a[1] * b[1])
        a, b = sorted((a, b))
        key = ("mul", a, b)
        if key not in self.cache:
            out = self.new(f"mul.{len(self.cache)}", "gate")
            self.cache[key] = out
            self.row([(1, [out]), (-1, [a, b])], "multiplication", out[1])
        return self.cache[key]

    def sum(self, values):
        out = ZERO
        for value in values:
            out = self.add(out, value)
        return out

    def product(self, values):
        out = ONE
        for value in values:
            out = self.mul(out, value)
        return out

    def square(self, a):
        return self.mul(a, a)

    def congruent(self, left, right, modulus, label, guard=None):
        qp, qm = self.fresh(label + ".qp"), self.fresh(label + ".qm")
        self.eq(self.add(left, self.mul(modulus, qp)),
                self.add(right, self.mul(modulus, qm)), label, guard)

    def norm(self, a, x, y, label, guard=None):
        # x^2 - (a^2-1)y^2 = 1, with only nonnegative evaluations.
        yy = self.square(y)
        self.eq(self.add(self.square(x), yy),
                self.add(ONE, self.mul(self.square(a), yy)), label, guard)

    def power(self, n, k):
        """The graph m=n^k.

        Three Boolean selectors guard the zero-exponent, positive-exponent
        zero-base, and positive-base/positive-exponent cases. The last case
        is the literal Pell-Matiyasevich certificate, with signed congruence
        quotients represented as differences of two natural numbers.
        In positive_powers mode the caller supplies the invariant n,k>0;
        the globally constructed equation proves this invariant at every
        call. Only the last case is then emitted.
        """
        key = (n, k)
        if key in self.powers:
            return self.powers[key]
        tag = f"pow{len(self.powers)}"
        start = len(self.variables)
        m = self.new(tag + ".output")
        self.powers[key] = m
        if self.positive_powers:
            e2 = None
        else:
            e0, e1, e2 = [self.new(tag + ".case" + str(i)) for i in range(3)]
            for e in (e0, e1, e2):
                self.row([(1, [e, e]), (-1, [e])], tag + ".boolean")
            self.row([(1, [e0]), (1, [e1]), (1, [e2]), (-1, [])], tag + ".one_case")
            self.eq(k, ZERO, tag + ".exponent_zero", e0)
            self.eq(m, ONE, tag + ".zero_power", e0)
            km1, nm1 = self.new(tag + ".kminus1"), self.new(tag + ".nminus1")
            kp = self.add(km1, ONE)
            self.eq(k, kp, tag + ".zero_base_exponent_positive", e1)
            self.eq(n, ZERO, tag + ".base_zero", e1)
            self.eq(m, ZERO, tag + ".zero_base_output", e1)
            self.eq(k, kp, tag + ".exponent_positive", e2)
            self.eq(n, self.add(nm1, ONE), tag + ".base_positive", e2)

        W, A, T, Z, X, Y = [self.new(tag + "." + s) for s in ("W", "A", "T", "Z", "X", "Y")]
        U, V, S, R, B = [self.new(tag + ".pell." + s) for s in ("U", "V", "S", "R", "B")]
        a2, yk, b2 = [self.new(tag + ".slack." + s) for s in ("a2", "yk", "b2")]
        self.eq(A, self.add(a2, TWO), tag + ".A_at_least_two", e2)
        self.eq(Y, self.add(k, yk), tag + ".index_at_most_Y", e2)
        self.eq(B, self.add(b2, TWO), tag + ".B_at_least_two", e2)
        self.norm(A, X, Y, tag + ".norm1", e2)
        self.norm(A, U, V, tag + ".norm2", e2)
        self.norm(B, S, R, tag + ".norm3", e2)
        q4 = self.new(tag + ".q4")
        fourY = self.mul(FOUR, Y)
        self.eq(B, self.add(ONE, self.mul(fourY, q4)), tag + ".B_mod_4Y", e2)
        vd = self.new(tag + ".Vquotient_minus1")
        self.eq(V, self.mul(self.square(Y), self.add(vd, ONE)), tag + ".V_positive_multiple", e2)
        self.congruent(B, A, U, tag + ".B_mod_U", e2)
        self.congruent(S, X, U, tag + ".S_mod_U", e2)
        self.congruent(R, k, fourY, tag + ".R_mod_4Y", e2)
        # Moving Y*n to the left avoids subtraction in the arithmetic gates.
        self.congruent(self.add(X, self.mul(Y, n)),
                       self.add(self.mul(Y, A), m), T, tag + ".power_congruence", e2)
        self.eq(self.product([TWO, A, n]),
                self.sum([T, self.square(n), ONE]), tag + ".T_definition", e2)
        gap, wn, wk = [self.new(tag + ".slack." + s) for s in ("gap", "wn", "wk")]
        self.eq(T, self.sum([m, gap, ONE]), tag + ".output_bound", e2)
        self.eq(W, self.add(n, wn), tag + ".base_bound", e2)
        self.eq(W, self.add(k, wk), tag + ".exponent_bound", e2)
        self.norm(self.add(W, ONE), A, self.mul(W, Z), tag + ".last_norm", e2)
        self.macro_log.append({"macro": "power", "output": m, "base": n, "exponent": k,
                               "first_variable": start, "end_variable": len(self.variables)})
        return m

    def binomial(self, n, k):
        key = (n, k)
        if key in self.binomials:
            return self.binomials[key]
        tag = f"choose{len(self.binomials)}"
        out = self.new(tag + ".output")
        self.binomials[key] = out
        if self.shared_digit_base is None:
            q = self.add(self.power(TWO, n), ONE)
        else:
            q = self.shared_digit_base
            slack = self.new(tag + ".shared_limit_slack")
            self.eq(self.shared_digit_limit, self.add(n, slack), tag + ".shared_digit_bound")
        numerator = self.power(self.add(q, ONE), n)
        denominator = self.power(q, k)
        h, r, rs, os = [self.new(tag + "." + s) for s in ("high", "remainder", "rslack", "oslack")]
        quotient = self.add(self.mul(q, h), out)
        self.eq(numerator, self.add(self.mul(denominator, quotient), r), tag + ".digit_division")
        self.eq(denominator, self.sum([r, rs, ONE]), tag + ".remainder_bound")
        self.eq(q, self.sum([out, os, ONE]), tag + ".digit_bound")
        self.macro_log.append({"macro": "binomial", "output": out, "n": n, "k": k})
        return out

    def factorial(self, n):
        if n in self.factorials:
            return self.factorials[n]
        tag = f"factorial{len(self.factorials)}"
        out = self.new(tag + ".output")
        self.factorials[n] = out
        shifted = self.add(n, TWO)
        radius = self.power(shifted, shifted)
        c = self.binomial(self.add(radius, n), n)
        numerator = self.power(self.add(radius, ONE), n)
        remainder, slack = self.new(tag + ".remainder"), self.new(tag + ".slack")
        self.eq(self.add(numerator, c), self.sum([self.mul(c, out), remainder, ONE]), tag + ".ceiling")
        self.eq(c, self.sum([remainder, slack, ONE]), tag + ".remainder_bound")
        self.macro_log.append({"macro": "factorial", "output": out, "n": n})
        return out

    def moduli_product(self, n, t):
        # q = ((n+1)t+1)^n+2 and B=(t^n*n!*C(q+n,n)) mod (tq-1).
        q = self.add(self.power(self.add(self.mul(self.add(n, ONE), t), ONE), n), TWO)
        numerator = self.product([self.power(t, n), self.factorial(n), self.binomial(self.add(q, n), n)])
        modulus = self.new("moduli_product.modulus")
        self.eq(self.add(modulus, ONE), self.mul(t, q), "moduli_product.modulus_definition")
        out, quotient, slack = [self.new("moduli_product." + s) for s in ("output", "quotient", "slack")]
        self.eq(numerator, self.add(self.mul(modulus, quotient), out), "moduli_product.division")
        self.eq(modulus, self.sum([out, slack, ONE]), "moduli_product.remainder_bound")
        return out

    def signed_sum(self, terms, env):
        positive, negative = [], []
        for term in terms:
            coefficient = term["coefficient"]
            val = self.product([const(abs(coefficient))] + [env[v] for v in term["monomial"]])
            (positive if coefficient >= 0 else negative).append(val)
        return self.sum(positive), self.sum(negative)

    def pair_add(self, a, b):
        return self.add(a[0], b[0]), self.add(a[1], b[1])

    def pair_mul(self, a, b):
        return (self.add(self.mul(a[0], b[0]), self.mul(a[1], b[1])),
                self.add(self.mul(a[0], b[1]), self.mul(a[1], b[0])))

    def pair_square(self, p):
        return self.add(self.square(p[0]), self.square(p[1])), self.product([TWO, p[0], p[1]])

    def source_pair(self, source, env, index, include_label_slacks):
        total = (ONE, ZERO)
        for branch in source["horn_branches"]:
            local = dict(env)
            for definition in branch["definitions"]:
                plus, minus = self.signed_sum(definition["value"], local)
                require(minus == ZERO, "wire definition is not nonnegative")
                local[definition["name"]] = plus
            branch_pair = (ZERO, ZERO)
            for residual in branch["residuals"]:
                branch_pair = self.pair_add(branch_pair, self.pair_square(self.signed_sum(residual, local)))
            total = self.pair_mul(total, branch_pair)
        M = self.add(env["M0"], ONE)
        weight = lambda name: self.add(ONE, self.mul(env[name], M))
        accumulator = (self.mul(env["Sp"], weight("v")),
                       self.product([env["S"], weight("p"), weight("q")]))
        rows = [accumulator]
        if include_label_slacks:
            rows += [(self.add(env[v], env["d" + v]), env["m"]) for v in ("p", "q", "v")]
        denominator = self.add(self.mul(self.add(index, ONE), env["y"]), ONE)
        nextdenom = self.add(denominator, env["y"])
        rows += [(env["x"], self.add(env["S"], self.mul(denominator, env["u"]))),
                 (denominator, self.sum([env["S"], env["r"], ONE])),
                 (env["x"], self.add(env["Sp"], self.mul(nextdenom, env["vq"]))),
                 (nextdenom, self.sum([env["Sp"], env["rp"], ONE]))]
        for row in rows:
            total = self.pair_add(total, self.pair_square(row))
        return total

    def export(self, source_sha, variant, inline_affine=True):
        # A natural gate with an affine nonnegative defining expression can
        # be substituted everywhere, preserving both degree two and existence
        # of natural witnesses. Only nonlinear products need gate variables.
        substitutions = {}
        eliminated = set()
        if inline_affine:
            for i in range(len(self.variables)):
                row_id = self.gates.get(i)
                if row_id is not None:
                    terms = self.rows[row_id]["terms"]
                    if all(len(mon) <= 1 for _, mon in terms):
                        affine = defaultdict(int)
                        output_coefficient = 0
                        for coefficient, monomial in terms:
                            if monomial == [i]:
                                output_coefficient += coefficient
                            elif not monomial:
                                affine[()] -= coefficient
                            else:
                                require(monomial[0] < i, "affine gate not triangular")
                                for mon, value in substitutions[monomial[0]].items():
                                    affine[mon] -= coefficient * value
                        require(output_coefficient == 1, "nonmonic affine gate")
                        affine = {mon: value for mon, value in affine.items() if value}
                        require(all(value >= 0 and len(mon) <= 1
                                    for mon, value in affine.items()),
                                "affine restoration must be nonnegative")
                        # A support cap prevents a small variable saving from
                        # causing enormous dense residual expansions. This is
                        # a size tradeoff, never a correctness requirement.
                        if len(affine) <= 4:
                            substitutions[i] = affine
                            eliminated.add(row_id)
                            continue
                substitutions[i] = {(i,): 1}
        else:
            substitutions = {i: {(i,): 1} for i in range(len(self.variables))}

        substituted_rows = []
        for row_id, row in enumerate(self.rows):
            if row_id in eliminated:
                continue
            polynomial = defaultdict(int)
            for coefficient, monomial in row["terms"]:
                partial = {(): coefficient}
                for variable in monomial:
                    multiplied = defaultdict(int)
                    for ma, ca in partial.items():
                        for mb, cb in substitutions[variable].items():
                            multiplied[tuple(sorted(ma + mb))] += ca * cb
                    partial = multiplied
                for mon, value in partial.items():
                    polynomial[mon] += value
            terms = [[value, list(mon)] for mon, value in sorted(polynomial.items()) if value]
            require(all(len(mon) <= 2 for value, mon in terms), "substitution raised row degree")
            if terms:
                substituted_rows.append({"label": row["label"], "terms": terms,
                                         "gate": row["gate"]})
        local_gates = {row["gate"]: i for i, row in enumerate(substituted_rows)
                       if row["gate"] is not None}
        # Drop unreachable definitional gates before counting the equation.
        needed_rows = {i for i, row in enumerate(substituted_rows) if row["gate"] is None}
        needed_vars = {j for i in needed_rows for _, mon in substituted_rows[i]["terms"] for j in mon}
        todo = list(needed_vars)
        while todo:
            v = todo.pop()
            row_id = local_gates.get(v)
            if row_id is None or row_id in needed_rows:
                continue
            needed_rows.add(row_id)
            for _, mon in substituted_rows[row_id]["terms"]:
                for w in mon:
                    if w not in needed_vars:
                        needed_vars.add(w)
                        todo.append(w)
        ordered = sorted(needed_vars)
        remap = {old: new for new, old in enumerate(ordered)}
        rows = [{"label": row["label"], "terms": [[c, [remap[i] for i in mon]] for c, mon in row["terms"]]}
                for i, row in enumerate(substituted_rows) if i in needed_rows]
        variables = [self.variables[i] for i in ordered]
        expanded = defaultdict(int)
        for row in rows:
            for ca, ma in row["terms"]:
                for cb, mb in row["terms"]:
                    expanded[tuple(sorted(ma + mb))] += ca * cb
        polynomial = [[c, list(mon)] for mon, c in sorted(expanded.items()) if c]
        degree = max(map(lambda term: len(term[1]), polynomial), default=0)
        metrics = {"variables": len(variables), "quadratic_rows": len(rows),
                   "exact_degree": degree, "expanded_monomials": len(polynomial),
                   "max_abs_row_coefficient": max(abs(c) for r in rows for c, m in r["terms"]),
                   "max_abs_expanded_coefficient": max(abs(c) for c, m in polynomial),
                   "variable_kinds": dict(Counter(v["kind"] for v in variables)),
                   "power_graphs": len(self.powers), "binomial_graphs": len(self.binomials),
                   "factorial_graphs": len(self.factorials),
                   "positive_power_specialization": self.positive_powers,
                   "affine_gate_variables_eliminated": len(eliminated),
                   "unused_variables_removed": len(self.variables) - len(variables) - len(eliminated)}
        equation = {"schema": "finite_quadratic_residuals_v1", "domain": "nonnegative integers",
                    "polynomial": "sum(square(row) for row in residuals)",
                    "source_commit": "08200eb10fde2db408c69dffd840d6920a569b1f",
                    "wire_eliminated_source_sha256": source_sha, "variant": variant,
                    "metrics": metrics, "variables": variables, "residuals": rows}
        return equation, {"schema": "sparse_integer_polynomial_v1", "domain": "nonnegative integers",
                          "variables": len(variables), "terms": polynomial}, metrics


def envelope_exponent(source):
    """Certify a pure-power envelope for the actual nonnegative source pair.

    For W>=4 and every source input <=W, each node is at most W**d:
    input d=1; constants 0/1 use d=0, 2..4 use d=1;
    addition uses max(d1,d2)+1 and multiplication uses d1+d2.
    This visits a DAG rather than expanding its enormous polynomial.
    """
    probe = Builder(positive_powers=True)
    names = ('t', 'x', 'y', 'm', 'M0', 'p', 'q', 'v', 'a', 'b', 'c', 'd', 'S', 'Sp', 'u', 'vq')
    env = {name: probe.new('envelope.' + name) for name in names}
    ep, fp = source_pair_calculus(probe, source, env, env['t'], False)
    output = probe.add(ep, fp)
    exponents = {}
    for i, variable in enumerate(probe.variables):
        if i not in probe.gates:
            exponents[i] = 1
    records = []
    def degree(atom):
        if atom[0] == 'c':
            require(0 <= atom[1] <= 4, 'envelope numeral outside declared bound')
            return 0 if atom[1] <= 1 else 1
        return exponents[atom[1]]
    for (op, a, b), result in probe.cache.items():
        d = max(degree(a), degree(b)) + 1 if op == 'add' else degree(a) + degree(b)
        exponents[result[1]] = d
        records.append({'op': op, 'a': list(a), 'b': list(b), 'output': result[1], 'exponent': d})
    return degree(output), {'inputs': [v['name'] for i,v in enumerate(probe.variables) if i not in probe.gates],
                            'nodes': records, 'output': list(output), 'exponent': degree(output)}


def fixed_power(b, base, exponent):
    """An ordinary fixed-exponent multiplication circuit."""
    result = ONE
    while exponent:
        if exponent & 1:
            result = b.mul(result, base)
        exponent //= 2
        if exponent:
            base = b.square(base)
    return result


def construct(source, variant="cofinal11", positive_powers=True, literal_calculus=True,
              use_envelope=True, shared_digits=True):
    require(variant == "cofinal11", "this construction uses the cofinal eleven-coordinate source")
    require(positive_powers and literal_calculus, "this delivered construction requires its proved positive literal source")
    b = Builder(positive_powers=positive_powers)
    if literal_calculus:
        b.source_pair = source_pair_calculus.__get__(b, Builder)
    params = {name: b.new(name + ("0" if positive_powers and name in ("t", "m") else ""),
                         "outer") for name in ("t", "x", "y", "m", "M0")}
    if positive_powers:
        params["t"] = b.add(params["t"], ONE)
        params["m"] = b.add(params["m"], ONE)
    t, x, y, m, M0 = [params[name] for name in ("t", "x", "y", "m", "M0")]
    if shared_digits:
        b.shared_digit_limit = b.add(b.new("digit.limit_minus1"), ONE)
        b.shared_digit_base = b.add(b.power(TWO, b.shared_digit_limit), ONE)
    b.eq(b.power(b.add(m, ONE), t), b.add(M0, ONE), "carrier_power")
    u0, r0, ut, rt = [b.new("endpoint." + name) for name in ("u0", "r0", "ut", "rt")]
    dt = b.add(b.mul(b.add(t, ONE), y), ONE)
    b.eq(x, b.add(b.add(M0, TWO), b.mul(b.add(y, ONE), u0)), "endpoint.first_quotient")
    b.eq(y, b.sum([M0, r0, TWO]), "endpoint.first_remainder")
    b.eq(x, b.add(ONE, b.mul(dt, ut)), "endpoint.last_quotient")
    b.eq(dt, b.add(rt, TWO), "endpoint.last_remainder")
    locals_ = ["p", "q", "v", "a", "b", "c", "d", "S", "Sp", "u", "vq"]
    use_slacks = False
    U = b.new("crt.extra_bound")
    V = b.sum([m, y, U])
    bounds = {name: m if name in ("p", "q", "v") else y if name in ("S", "Sp") else V for name in locals_}
    encoded = {name: b.new("crt.encoded." + name) for name in locals_}
    if positive_powers:
        encoded = {name: b.add(a, ONE) for name, a in encoded.items()}
    C = b.new("crt.encoded_index")
    if use_envelope:
        exponent, envelope = envelope_exponent(source)
        W = b.sum([t, x, y, m, M0, V, FOUR])
        H = b.sum([fixed_power(b, W, exponent), t, V, ONE])
        b.envelope_certificate = envelope
    else:
        ep, fp = b.source_pair(source, params | bounds, t, use_slacks)
        H = b.sum([ep, fp, t, V, ONE])
    T = b.factorial(H)
    B = b.moduli_product(t, T)
    for name in locals_:
        chosen = b.binomial(encoded[name], b.add(bounds[name], ONE))
        quotient = b.new("crt.range_quotient." + name)
        b.eq(chosen, b.mul(B, quotient), "crt.factorial_free_range." + name)
    qi = b.new("crt.index_quotient")
    b.eq(b.add(ONE, b.mul(b.add(C, ONE), T)), b.mul(B, qi), "crt.index")
    encoded_e, encoded_f = b.source_pair(source, params | encoded, C, use_slacks)
    b.congruent(encoded_e, encoded_f, B, "crt.evaluation")
    return b


def write_json(path, data):
    payload = (json.dumps(data, separators=(",", ":"), sort_keys=True) + "\n").encode()
    path.write_bytes(payload)
    return sha256(payload).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=Path(__file__).with_name("wire_eliminated_source.json"))
    parser.add_argument("--output", type=Path, default=Path(__file__).parent)
    parser.add_argument("--variant", choices=("cofinal11",), default="cofinal11")
    parser.add_argument("--original-majorant", action="store_true",
                        help="retain evaluation of E+F at the witness bounds")
    parser.add_argument("--individual-digits", action="store_true",
                        help="retain one exponential digit base per binomial graph")
    parser.add_argument("--keep-linear-wires", action="store_true",
                        help="retain affine gate variables as a comparison construction")
    args = parser.parse_args()
    source_bytes = args.source.read_bytes()
    source = json.loads(source_bytes)
    builder = construct(source, args.variant, use_envelope=not args.original_majorant,
                        shared_digits=not args.individual_digits)
    equation, polynomial, metrics = builder.export(sha256(source_bytes).hexdigest(), args.variant,
                                                  inline_affine=not args.keep_linear_wires)
    args.output.mkdir(parents=True, exist_ok=True)
    hashes = {"equation.json": write_json(args.output / "equation.json", equation),
              "expanded_polynomial.json": write_json(args.output / "expanded_polynomial.json", polynomial)}
    if hasattr(builder, "envelope_certificate"):
        hashes["envelope_certificate.json"] = write_json(args.output / "envelope_certificate.json", builder.envelope_certificate)
    receipt = {"status": "PASS", "variant": args.variant, "metrics": metrics, "sha256": hashes,
               "source_sha256": sha256(source_bytes).hexdigest(),
               "builder_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
               "literal_calculus_sha256": sha256(Path(__file__).with_name("direct_calculus.py").read_bytes()).hexdigest(),
               "literal_calculus_used": True,
               "source_reduction": "cofinal beta digits bounded by y; two remainder coordinates deleted",
               "binomial_digit_base": "individual" if args.individual_digits else "one shared q=2^L+1 with every upper argument <=L",
               "envelope_exponent": getattr(builder, "envelope_certificate", {}).get("exponent"),
               "scope": "finite materialization and exact expansion; mathematical soundness in report"}
    (args.output / "BUILD.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

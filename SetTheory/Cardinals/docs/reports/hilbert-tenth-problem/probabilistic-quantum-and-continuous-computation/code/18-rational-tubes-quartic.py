"""Unrolled quadratic-residual / quartic-SOS compiler.

The output polynomial is stored as a list of residuals whose squares are summed.
It is an explicit ordinary polynomial in circuit form, NOT an MRDP extractor.
"""
from __future__ import annotations
from dataclasses import dataclass
import sympy as sp
from tubes import Instance, Certificate, verify


@dataclass(frozen=True)
class Wire:
    expression: sp.Expr
    value: int


def constant(n: int) -> Wire:
    return Wire(sp.Integer(n), n)


class Compiler:
    def __init__(self, parameters: dict[str, int]):
        self.parameters = {sp.Symbol(k): v for k, v in parameters.items()}
        self.witness: dict[sp.Symbol, int] = {}
        self.residuals: list[sp.Expr] = []
        self.labels: list[str] = []
        self.gates = 0

    def natural(self, name: str, value: int) -> Wire:
        if value < 0:
            raise ValueError(f"negative natural witness {name}")
        symbol = sp.Symbol(name)
        if symbol in self.witness or symbol in self.parameters:
            raise ValueError(f"duplicate variable {name}")
        self.witness[symbol] = value
        return Wire(symbol, value)

    def residual(self, expression: sp.Expr, label: str) -> None:
        self.residuals.append(sp.expand(expression))
        self.labels.append(label)

    def signed(self, name: str, value: int) -> Wire:
        p = self.natural(name + "p", max(value, 0))
        n = self.natural(name + "n", max(-value, 0))
        self.residual(p.expression * n.expression, name + ":canonical")
        return Wire(p.expression - n.expression, value)

    def gate(self, op: str, x: Wire, y: Wire) -> Wire:
        self.gates += 1
        expr = x.expression + y.expression if op == "+" else x.expression * y.expression
        value = x.value + y.value if op == "+" else x.value * y.value
        z = self.signed(f"g{self.gates}", value)
        self.residual(z.expression - expr, f"g{self.gates}:{op}")
        return z

    def add(self, x: Wire, y: Wire) -> Wire:
        return self.gate("+", x, y)

    def mul(self, x: Wire, y: Wire) -> Wire:
        return self.gate("*", x, y)

    def power(self, x: Wire, exponent: int) -> Wire:
        if exponent == 0:
            return constant(1)
        if exponent == 1:
            return x
        half = self.power(x, exponent // 2)
        squared = self.mul(half, half)
        return self.mul(squared, x) if exponent % 2 else squared

    def sum(self, terms: list[Wire]) -> Wire:
        if not terms:
            return constant(0)
        result = terms[0]
        for term in terms[1:]:
            result = self.add(result, term)
        return result

    def positive(self, expression: sp.Expr, value: int, label: str) -> None:
        slack = self.natural(label, value - 1)
        self.residual(expression - 1 - slack.expression, label + ":strict")

    def export(self) -> dict:
        values = self.parameters | self.witness
        degrees, evaluations = [], []
        for residual in self.residuals:
            if residual == 0:
                degrees.append(0)
                evaluations.append(0)
            else:
                poly = sp.Poly(residual, *sorted(residual.free_symbols, key=str))
                degrees.append(int(poly.total_degree()))
                evaluations.append(int(residual.xreplace(values)))
        assert max(degrees, default=0) <= 2
        assert not any(evaluations)
        return {"parameters": {str(k): v for k, v in self.parameters.items()},
                "witness": {str(k): v for k, v in self.witness.items()},
                "gate_count": self.gates, "witness_count": len(self.witness),
                "equation_count": len(self.residuals),
                "maximum_residual_degree": max(degrees, default=0),
                "quartic_definition": "P = sum(residual[i]**2 for every i)",
                "residuals": [str(p) for p in self.residuals],
                "labels": self.labels, "all_residuals_zero": not any(evaluations)}


def compile_certificate(instance: Instance, cert: Certificate) -> dict:
    verify(instance, cert)
    n, dim = cert.steps, instance.dimension
    mrows, degree = len(instance.target), instance.degree
    c = Compiler({"R": cert.radius, "H": cert.inverse_step, "D": cert.scale})
    r, h, d = [Wire(sp.Symbol(name), value) for name, value in
               (("R", cert.radius), ("H", cert.inverse_step), ("D", cert.scale))]
    for name, wire in (("R", r), ("H", h), ("D", d)):
        c.positive(wire.expression, wire.value, "positive_" + name)
    m = c.sum([c.mul(constant(abs(a)), c.power(r, sum(alpha)))
               for p in instance.polynomials for a, alpha in p])
    ell = c.sum([c.mul(constant(abs(a) * sum(alpha)),
                       c.power(r, sum(alpha) - 1))
                 for p in instance.polynomials for a, alpha in p if sum(alpha)])
    q = c.mul(c.mul(constant(instance.denominator), h), c.power(d, degree - 1))
    b = c.mul(h, h)
    k = c.mul(h, c.add(h, ell))
    dm = c.mul(d, m)
    j = constant(cert.forcing_units)
    offset = c.add(c.add(c.mul(ell, c.add(dm, j)), b), c.mul(j, h))
    guard_base = c.add(c.add(c.mul(c.mul(d, r), h), c.mul(constant(-1), dm)),
                       constant(-cert.forcing_units))
    nodes = [c.signed(f"X0_{a}", v) for a, v in enumerate(cert.nodes[0])]
    for a, (x, v) in enumerate(zip(instance.initial, nodes)):
        c.residual(x.denominator * v.expression - x.numerator * d.expression,
                   f"initial:{a}")
    error = constant(cert.initial_error_units)
    for i in range(n):
        values = []
        for p in instance.polynomials:
            terms = []
            for coefficient, alpha in p:
                term = constant(coefficient)
                for x, exponent in zip(nodes, alpha):
                    if exponent:
                        term = c.mul(term, c.power(x, exponent))
                if degree - sum(alpha):
                    term = c.mul(term, c.power(d, degree - sum(alpha)))
                terms.append(term)
            values.append(c.sum(terms))
        new_nodes = []
        for a, (x, tilde) in enumerate(zip(nodes, values)):
            y = c.signed(f"X{i+1}_{a}", cert.nodes[i + 1][a])
            u = c.natural(f"U{i}_{a}", cert.floor_remainders[i][a])
            slack = c.natural(f"Us{i}_{a}", q.value - u.value - 1)
            c.residual(q.expression * (y.expression - x.expression) +
                       u.expression - tilde.expression, f"floor:{i}:{a}")
            c.residual(u.expression + slack.expression + 1 - q.expression,
                       f"floor_bound:{i}:{a}")
            for sign in (-1, 1):
                c.positive(guard_base.expression - h.expression * error.expression +
                           sign * h.expression * x.expression,
                           guard_base.value - h.value * error.value + sign * h.value * x.value,
                           f"guard{i}_{a}_{'plus' if sign == 1 else 'minus'}")
            new_nodes.append(y)
        next_error = c.natural(f"E{i+1}", cert.errors[i + 1])
        v = c.natural(f"V{i}", cert.ceiling_remainders[i])
        vs = c.natural(f"Vs{i}", b.value - v.value - 1)
        c.residual(b.expression * next_error.expression - k.expression * error.expression -
                   offset.expression - v.expression, f"radius:{i}")
        c.residual(v.expression + vs.expression + 1 - b.expression, f"radius_bound:{i}")
        nodes, error = new_nodes, next_error
    for row_index, (row, bound) in enumerate(instance.target):
        expr = bound * d.expression - sum(a * x.expression for a, x in zip(row, nodes)) - \
               sum(abs(a) for a in row) * error.expression
        value = bound * d.value - sum(a * x.value for a, x in zip(row, nodes)) - \
                sum(abs(a) for a in row) * error.value
        c.positive(expr, value, f"target{row_index}")
    result = c.export()
    expected_witnesses = 2*c.gates + (6*dim+3)*n + 2*dim + mrows + 3
    expected_equations = 2*c.gates + (5*dim+2)*n + 2*dim + mrows + 3
    assert result["witness_count"] == expected_witnesses
    assert result["equation_count"] == expected_equations
    result["count_formula_verified"] = True
    return result


def count_gates(instance: Instance, steps: int) -> int:
    """Exact syntactic gate count for the current compiler, without materialization."""
    if type(steps) is not int or steps <= 0:
        raise ValueError("positive integral steps required")
    def power_cost(exponent: int) -> int:
        return 0 if exponent <= 1 else power_cost(exponent // 2) + 1 + exponent % 2
    degrees = [sum(alpha) for p in instance.polynomials for _, alpha in p]
    m_cost = sum(1 + power_cost(a) for a in degrees) + max(0, len(degrees)-1)
    nonconstant = [a for a in degrees if a > 0]
    l_cost = sum(1 + power_cost(a-1) for a in nonconstant) + max(0, len(nonconstant)-1)
    global_cost = m_cost + l_cost + 16 + power_cost(instance.degree-1)
    field_cost = 0
    for polynomial in instance.polynomials:
        field_cost += max(0, len(polynomial)-1)
        for _, alpha in polynomial:
            field_cost += sum(1 + power_cost(a) for a in alpha if a)
            gap = instance.degree-sum(alpha)
            if gap:
                field_cost += 1 + power_cost(gap)
    return global_cost + steps * field_cost

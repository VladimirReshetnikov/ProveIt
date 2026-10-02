"""Exact, canonical, quadratic certificates for bounded random-access memory.

This is an actual sparse-polynomial generator over N, not a hash modulo a
prime. A JSON export contains all quadratic residuals, the parameter/witness
split, and an example zero.  The optional quartic export is their expanded SOS.
It implements the MEMORY component of the paper; the entire six-rule bounded
interaction-net compiler is specified and proved in the paper, not expanded here.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Iterable

Monomial = tuple[int, ...]


def decimal_natural(value: int) -> str:
    """Decimal export without changing Python's global large-int safety limit.

    Certificate values can legitimately exceed Python 3.11+'s default limit
    for one int-to-decimal conversion. Small base-10**9 chunks avoid that
    limit while preserving exact, ordinary decimal JSON strings.
    """
    if type(value) is not int or value < 0:
        raise ValueError("decimal_natural requires a nonnegative integer")
    if value == 0:
        return "0"
    chunks: list[int] = []
    while value:
        value, remainder = divmod(value, 1_000_000_000)
        chunks.append(remainder)
    return str(chunks[-1]) + "".join(f"{part:09d}" for part in reversed(chunks[:-1]))


@dataclass
class Poly:
    terms: dict[Monomial, int]

    @staticmethod
    def const(x: int) -> "Poly":
        return Poly({(): x} if x else {})

    @staticmethod
    def variable(i: int) -> "Poly":
        return Poly({(i,): 1})

    def __add__(self, other):
        if isinstance(other, int):
            other = Poly.const(other)
        result = dict(self.terms)
        for m, c in other.terms.items():
            result[m] = result.get(m, 0) + c
            if not result[m]:
                del result[m]
        return Poly(result)

    __radd__ = __add__

    def __neg__(self):
        return Poly({m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        return self + (-other if isinstance(other, Poly) else -int(other))

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        if isinstance(other, int):
            other = Poly.const(other)
        result: dict[Monomial, int] = {}
        for a, ca in self.terms.items():
            for b, cb in other.terms.items():
                m = tuple(sorted(a + b))
                result[m] = result.get(m, 0) + ca * cb
        return Poly({m: c for m, c in result.items() if c})

    __rmul__ = __mul__

    def evaluate(self, values: list[int]) -> int:
        result = 0
        for m, c in self.terms.items():
            term = c
            for i in m:
                term *= values[i]
            result += term
        return result

    @property
    def degree(self) -> int:
        return max(map(len, self.terms), default=0)

    def sparse(self) -> list:
        return [[list(m), c] for m, c in sorted(self.terms.items())]


class Circuit:
    def __init__(self):
        self.names: list[str] = []
        self.values: list[int] = []
        self.roles: list[str] = []
        self.residuals: list[Poly] = []
        self.labels: list[str] = []

    def variable(self, name: str, value: int, role: str = "witness") -> Poly:
        if type(value) is not int or value < 0:
            raise ValueError(f"nonnegative integer required for {name}")
        if name in self.names:
            raise ValueError(f"duplicate variable name {name}")
        i = len(self.names)
        self.names.append(name)
        self.values.append(value)
        self.roles.append(role)
        return Poly.variable(i)

    def eq(self, residual: Poly, label: str) -> None:
        if residual.degree > 2:
            raise ValueError("only quadratic residuals are allowed")
        self.residuals.append(residual)
        self.labels.append(label)

    def bound(self, x: Poly, exclusive: int, name: str) -> None:
        value = x.evaluate(self.values)
        if not 0 <= value < exclusive:
            raise ValueError(f"{name} out of bounds")
        slack = self.variable(name + ".slack", exclusive - 1 - value)
        self.eq(x + slack - (exclusive - 1), name + ".range")

    def gate(self, expr: Poly, name: str) -> Poly:
        z = self.variable(name, expr.evaluate(self.values))
        self.eq(z - expr, name + ".definition")
        return z

    def product(self, factors: list[Poly], prefix: str) -> Poly:
        if not factors:
            return Poly.const(1)
        level = 0
        while len(factors) > 1:
            next_level = []
            for i in range(0, len(factors), 2):
                if i + 1 == len(factors):
                    next_level.append(factors[i])
                else:
                    next_level.append(self.gate(factors[i] * factors[i+1],
                                               f"{prefix}.{level}.{i//2}"))
            factors, level = next_level, level + 1
        return factors[0]

    def power(self, base: int, exponent: int, prefix: str) -> Poly:
        z = Poly.const(1)
        for j, bit in enumerate(bin(exponent)[2:]):
            z = self.gate(z*z, f"{prefix}.square{j}")
            if bit == "1":
                z = self.gate(base*z, f"{prefix}.times_base{j}")
        return z

    def failures(self, values: list[int] | None = None) -> list[str]:
        values = self.values if values is None else values
        if any(type(v) is not int or v < 0 for v in values):
            return ["natural-number domain"]
        return [name for p, name in zip(self.residuals, self.labels) if p.evaluate(values)]

    def sos(self) -> Poly:
        return sum((p*p for p in self.residuals), Poly.const(0))

    def stats(self) -> dict:
        witnesses = [v for v, r in zip(self.values, self.roles) if r == "witness"]
        return {"parameters": self.roles.count("parameter"),
                "witnesses": self.roles.count("witness"),
                "quadratic_residuals": len(self.residuals),
                "maximum_residual_degree": max((p.degree for p in self.residuals), default=0),
                "maximum_witness_bits": max((max(1, v.bit_length()) for v in witnesses), default=0),
                "total_witness_bits": sum(max(1, v.bit_length()) for v in witnesses),
                "failed_residuals": self.failures()}

    def export(self, include_quartic: bool = True) -> dict:
        ans = {"domain": "natural numbers including zero",
               "scope": "exact bounded-memory component, not the full interaction-net compiler",
               "variables": [{"id": i, "name": n, "role": r, "value": decimal_natural(v)}
                             for i, (n, r, v) in enumerate(zip(self.names, self.roles, self.values))],
               "quadratic_residuals": [{"name": n, "terms": p.sparse()}
                                       for p, n in zip(self.residuals, self.labels)],
               "statistics": self.stats()}
        if include_quartic:
            p = self.sos()
            ans["quartic_sum_of_squares"] = {"degree": p.degree, "terms": p.sparse()}
        return ans


def build_memory(initial: list[int], events: list[tuple[int, int, int]],
                 final: list[int], value_bound: int) -> tuple[Circuit, dict]:
    """Compile memory consistency for (address, old value, new value) events.

    Initial and final contents and event fields are parameters. Their designated
    example values may be inconsistent: then some residuals will be nonzero.
    Ranges and address/time uniqueness are part of the construction.
    """
    A, m = len(initial), len(events)
    if A < 1 or len(final) != A or type(value_bound) is not int or value_bound < 2:
        raise ValueError("need equal nonempty memories and value_bound >= 2")
    V, H = value_bound, m + 2
    L, U = 2*A + m, A*H*V*V
    c = Circuit()
    ini = [c.variable(f"input.initial.{a}", v, "parameter") for a, v in enumerate(initial)]
    fin = [c.variable(f"input.final.{a}", v, "parameter") for a, v in enumerate(final)]
    for a in range(A):
        c.bound(ini[a], V, f"initial.{a}")
        c.bound(fin[a], V, f"final.{a}")
    raw: list[list[Poly]] = [[Poly.const(a), Poly.const(0), Poly.const(0), ini[a]]
                            for a in range(A)]
    for j, (address, old, new) in enumerate(events):
        fields = [c.variable(f"input.event.{j}.{name}", v, "parameter")
                  for name, v in zip(("address", "old", "new"), (address, old, new))]
        for p, lim, name in zip(fields, (A, V, V), ("address", "old", "new")):
            c.bound(p, lim, f"event.{j}.{name}")
        raw.append([fields[0], Poly.const(j + 1), fields[1], fields[2]])
    raw += [[Poly.const(a), Poly.const(m+1), fin[a], fin[a]] for a in range(A)]
    concrete = [[p.evaluate(c.values) for p in row] for row in raw]
    ordered_values = sorted(concrete, key=lambda r: (r[0], r[1]))
    ordered: list[list[Poly]] = []
    for j, row in enumerate(ordered_values):
        ps = [c.variable(f"sorted.{j}.{name}", v)
              for name, v in zip(("address", "time", "old", "new"), row)]
        for p, lim, name in zip(ps, (A, H, V, V), ("address", "time", "old", "new")):
            c.bound(p, lim, f"sorted.{j}.{name}")
        ordered.append(ps)
    for j in range(L-1):
        a, t, r, w = ordered[j]
        an, tn, rn, wn = ordered[j+1]
        key, keyn = H*a+t, H*an+tn
        gap = keyn.evaluate(c.values)-key.evaluate(c.values)-1
        s = c.variable(f"key_gap.{j}", gap)
        c.eq(key + 1 + s-keyn, f"strict_key_order.{j}")
        same_value = int(ordered_values[j][0] == ordered_values[j+1][0])
        z = c.variable(f"same_address.{j}", same_value)
        d = c.variable(f"address_gap.{j}", 0 if same_value else
                       ordered_values[j+1][0]-ordered_values[j][0]-1)
        c.eq(z*(z-1), f"same_boolean.{j}")
        c.eq(an-a-(1-z)*(d+1), f"address_relation.{j}")
        c.eq(z*d, f"unused_gap_zero.{j}")
        c.eq(z*(rn-w), f"memory_link.{j}")
    def packed(row: list[Poly]) -> Poly:
        a, t, r, w = row
        return H*V*V*a + V*V*t + V*r + w
    base = c.gate(c.power(U, L, "base_power")+1, "base")
    left = c.product([base+packed(row) for row in raw], "left_product")
    right = c.product([base+packed(row) for row in ordered], "right_product")
    c.eq(left-right, "exact_multiset_equality")
    return c, {"addresses": A, "ordinary_events": m, "records": L,
               "time_radix": H, "value_radix": V, "record_bound": U,
               "base_definition": f"{U}^{L}+1", "sorted_records": ordered_values}

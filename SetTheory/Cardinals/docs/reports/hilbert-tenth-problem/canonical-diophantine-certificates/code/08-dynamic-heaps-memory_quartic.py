#!/usr/bin/env python3
"""Exact, witness-faithful Diophantine certificates for finite memory logs.

All variables range over N = {0,1,...}.  Equations have integer coefficients.
The output polynomial is the sum of the squares of the emitted residuals.
Only the Python standard library is required. No finite-field hashing is used.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Iterable, Sequence
import argparse
import json
from pathlib import Path


class Poly:
    """Sparse integer polynomial; monomials are sorted tuples of variable IDs."""
    __slots__ = ("terms",)

    def __init__(self, terms: dict[tuple[int, ...], int] | None = None):
        self.terms = {m: c for m, c in (terms or {}).items() if c}

    @staticmethod
    def coerce(x: Poly | int) -> Poly:
        if isinstance(x, Poly):
            return x
        if isinstance(x, int):
            return Poly({(): x})
        raise TypeError(f"Expected polynomial or int, got {type(x)}")

    def __add__(self, other: Poly | int) -> Poly:
        out = self.terms.copy()
        for m, c in self.coerce(other).terms.items():
            out[m] = out.get(m, 0) + c
        return Poly(out)

    __radd__ = __add__

    def __neg__(self) -> Poly:
        return Poly({m: -c for m, c in self.terms.items()})

    def __sub__(self, other: Poly | int) -> Poly:
        return self + -self.coerce(other)

    def __rsub__(self, other: Poly | int) -> Poly:
        return self.coerce(other) + -self

    def __mul__(self, other: Poly | int) -> Poly:
        out: dict[tuple[int, ...], int] = {}
        for m, a in self.terms.items():
            for n, b in self.coerce(other).terms.items():
                k = tuple(sorted(m + n))
                out[k] = out.get(k, 0) + a * b
        return Poly(out)

    __rmul__ = __mul__

    @property
    def degree(self) -> int:
        return max(map(len, self.terms), default=0)

    def evaluate(self, values: Sequence[int]) -> int:
        result = 0
        for monomial, coefficient in self.terms.items():
            term = coefficient
            for i in monomial:
                term *= values[i]
            result += term
        return result

    def data(self) -> list[dict]:
        return [{"coefficient": c, "variables": list(m)}
                for m, c in sorted(self.terms.items())]


@dataclass(frozen=True)
class Event:
    address: int
    write: int
    value: int

    def __post_init__(self):
        for name in ("address", "write", "value"):
            v = getattr(self, name)
            if not isinstance(v, int) or v < 0:
                raise ValueError(f"{name} must be a nonnegative integer")
        if self.write not in (0, 1):
            raise ValueError("write must be 0 (read) or 1 (write)")


class Certificate:
    def __init__(self):
        self.names: list[str] = []
        self.roles: list[str] = []
        self.witness: list[int] = []
        self.residuals: list[tuple[str, Poly]] = []
        self.meta: dict[str, int | str] = {}

    def variable(self, name: str, value: int, role: str = "aux") -> Poly:
        if not isinstance(value, int) or value < 0:
            raise ValueError(f"Invalid natural witness {name}={value}")
        i = len(self.names)
        self.names.append(name)
        self.roles.append(role)
        self.witness.append(value)
        return Poly({(i,): 1})

    def equation(self, label: str, residual: Poly | int):
        p = Poly.coerce(residual)
        if p.degree > 2:
            raise ValueError(f"Nonquadratic residual: {label}")
        self.residuals.append((label, p))

    def failures(self, values: Sequence[int] | None = None) -> list[str]:
        v = self.witness if values is None else values
        if len(v) != len(self.names):
            return ["wrong assignment length"]
        if any(not isinstance(x, int) or x < 0 for x in v):
            return ["assignment is not in the natural-number domain"]
        return [name for name, p in self.residuals if p.evaluate(v) != 0]

    def energy(self, values: Sequence[int] | None = None) -> int:
        v = self.witness if values is None else values
        return sum(p.evaluate(v) ** 2 for _, p in self.residuals)

    def data(self) -> dict:
        return {
            "format": "integer-sum-of-squares-v1",
            "domain": "nonnegative integers",
            "polynomial": "sum(residual**2 for residual in residuals)",
            "metadata": self.meta,
            "variables": [{"name": n, "role": r, "value": v}
                          for n, r, v in zip(self.names, self.roles, self.witness)],
            "residuals": [{"label": n, "terms": p.data()}
                          for n, p in self.residuals],
        }


def bitonic_network(n: int) -> list[tuple[int, int, bool]]:
    """Return comparators (i,j,ascending), for a power-of-two wire count."""
    if n < 1 or n & (n - 1):
        raise ValueError("wire count must be a positive power of two")
    out = []
    span = 2
    while span <= n:
        stride = span // 2
        while stride:
            for i in range(n):
                j = i ^ stride
                if j > i:
                    out.append((i, j, (i & span) == 0))
            stride //= 2
        span *= 2
    return out


def legal_log(events: Iterable[Event]) -> bool:
    memory: dict[int, int] = {}
    for e in events:
        if e.write:
            memory[e.address] = e.value
        elif e.value != memory.get(e.address, 0):
            return False
    return True


def compile_log(events: Sequence[Event]) -> Certificate:
    """Emit a fixed-shape polynomial plus its canonical candidate witness.

    For a fixed log length, the polynomial is independent of event values.
    Source addresses/flags/values are variables, not hard-coded coefficients.
    An invalid log produces an assignment failing at least one read equation.
    """
    events = list(events)
    cert = Certificate()
    m = len(events)
    if not m:
        cert.meta = {"events": 0, "padded_events": 0, "comparators": 0,
                     "source_variables": 0, "aux_variables": 0, "equations": 0, "degree_bound": 4}
        return cert
    n = 1 << (m - 1).bit_length()
    padded = events + [Event(0, 1, 0) for _ in range(n - m)]
    records: list[list[Poly]] = []
    actual: list[list[int]] = []
    # Record layout: [key, address, write flag, access value].
    for t, e in enumerate(padded):
        if t < m:
            a = cert.variable(f"src_{t}_address", e.address, "source")
            w = cert.variable(f"src_{t}_write", e.write, "source")
            v = cert.variable(f"src_{t}_value", e.value, "source")
        else:
            a, w, v = Poly.coerce(0), Poly.coerce(1), Poly.coerce(0)
        kval = n * e.address + t
        key = cert.variable(f"key_{t}", kval)
        cert.equation(f"key_{t}", key - n * a - t)
        cert.equation(f"flag_{t}", w * (w - 1))
        records.append([key, a, w, v])
        actual.append([kval, e.address, e.write, e.value])
    network = bitonic_network(n)
    for g, (i, j, ascending) in enumerate(network):
        x, y = records[i], records[j]
        xv, yv = actual[i], actual[j]
        if xv[0] == yv[0]:
            raise AssertionError("timestamp keys must be distinct")
        bv = int(xv[0] < yv[0])
        b = cert.variable(f"cmp_{g}_b", bv)
        h = cert.variable(f"cmp_{g}_h", abs(yv[0] - xv[0]) - 1)
        cert.equation(f"cmp_{g}_bool", b * (b - 1))
        cert.equation(f"cmp_{g}_order", (2*b - 1)*(y[0] - x[0]) - h - 1)
        lo, hi = [], []
        lov, hiv = (xv[:], yv[:]) if bv else (yv[:], xv[:])
        for f in range(4):
            l = cert.variable(f"cmp_{g}_lo_{f}", lov[f])
            u = cert.variable(f"cmp_{g}_hi_{f}", hiv[f])
            cert.equation(f"cmp_{g}_low_{f}", l - b*x[f] - (1-b)*y[f])
            cert.equation(f"cmp_{g}_high_{f}", u - (1-b)*x[f] - b*y[f])
            lo.append(l)
            hi.append(u)
        records[i], records[j] = (lo, hi) if ascending else (hi, lo)
        actual[i], actual[j] = (lov, hiv) if ascending else (hiv, lov)
    cert.equation("first_read", (1-records[0][2])*records[0][3])
    for i in range(1, n):
        previous, current = records[i-1], records[i]
        pv, cv = actual[i-1], actual[i]
        delta = cv[1] - pv[1]
        if delta < 0:
            raise AssertionError("sorting network did not sort addresses")
        zv = int(delta == 0)
        z = cert.variable(f"scan_{i}_same", zv)
        h = cert.variable(f"scan_{i}_gap", 0 if zv else delta-1)
        carry = cert.variable(f"scan_{i}_carry", zv * pv[3])
        cert.equation(f"scan_{i}_bool", z*(z-1))
        cert.equation(f"scan_{i}_gap", current[1]-previous[1]-(1-z)*(h+1))
        cert.equation(f"scan_{i}_inactive", z*h)
        cert.equation(f"scan_{i}_carry", carry-z*previous[3])
        cert.equation(f"scan_{i}_read", (1-current[2])*(current[3]-carry))
    c = len(network)
    aux = cert.roles.count("aux")
    assert aux == 10*c + 4*n - 3
    assert len(cert.residuals) == 10*c + 7*n - 4
    cert.meta = {"events": m, "padded_events": n, "comparators": c,
                 "source_variables": 3*m, "aux_variables": aux,
                 "equations": len(cert.residuals), "degree_bound": 4}
    return cert


def verify_export(data: dict) -> bool:
    """Independent evaluation of an exported certificate (no compiler calls).

    This checks an assignment to the supplied residual system. The caller must
    separately trust/rebuild the compiler to bind that system to the semantics.
    """
    try:
        values = [x["value"] for x in data["variables"]]
        if any(not isinstance(x, int) or x < 0 for x in values):
            return False
        for equation in data["residuals"]:
            residual = 0
            for term in equation["terms"]:
                product = term["coefficient"]
                if not isinstance(product, int):
                    return False
                ids = term["variables"]
                if len(ids) > 2:
                    return False
                for i in ids:
                    if not isinstance(i, int) or i < 0 or i >= len(values):
                        return False
                    product *= values[i]
                residual += product
            if residual:
                return False
        return True
    except (KeyError, TypeError, IndexError):
        return False


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--events", type=Path,
                        help="JSON list of [address,write_flag,value]")
    parser.add_argument("--output", type=Path, default=Path("certificate.json"))
    args = parser.parse_args()
    try:
        rows = json.loads(args.events.read_text(encoding="utf-8")) if args.events else [
            [7, 1, 4], [2, 0, 0], [7, 0, 4], [7, 1, 9], [7, 0, 9]]
        if not isinstance(rows, list) or any(
                not isinstance(r, list) or len(r) != 3 for r in rows):
            raise ValueError("events must be a JSON list of three-element lists")
        events = [Event(*r) for r in rows]
        cert = compile_log(events)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(cert.data(), indent=2) + "\n", encoding="utf-8")
    except (OSError, ValueError, TypeError) as exc:
        parser.error(str(exc))
    print(json.dumps({**cert.meta, "valid": not cert.failures(),
                      "energy": cert.energy()}, indent=2))


if __name__ == "__main__":
    main()

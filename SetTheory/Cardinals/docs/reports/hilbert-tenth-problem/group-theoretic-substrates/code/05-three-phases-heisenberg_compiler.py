#!/usr/bin/env python3
"""Exact three-phase compiler for integral quadratic systems.

Python 3.10+, standard library only. No floating-point arithmetic, network,
or external theorem prover is used. The accompanying article gives the proof.

CLI: python heisenberg_compiler.py spec.json output.json
JSON input: {"n": n, "rows": [{"constant": c, "linear": [...],
"diagonal": [...], "cross": [[i,j,coefficient], ...]}, ...]}.
Indices are zero-based; cross pairs must satisfy i < j and be unique.
The output specifies all three generator bases in H^N x Z^m.
"""
from __future__ import annotations
from dataclasses import dataclass
import argparse
import json
from pathlib import Path
from typing import Sequence

Vector = tuple[int, ...]
Matrix = tuple[Vector, ...]
H = tuple[int, int, int]


def integer(v: object) -> int:
    if type(v) is not int:
        raise TypeError(f"An exact integer is required, not {type(v).__name__}")
    return v


def vector(v: Sequence[int], length: int | None = None) -> Vector:
    out = tuple(integer(a) for a in v)
    if length is not None and len(out) != length:
        raise ValueError(f"Expected {length} coordinates, got {len(out)}")
    return out


def choose2(t: int) -> int:
    integer(t)
    return t * (t - 1) // 2


def matvec(a: Matrix, x: Vector) -> Vector:
    if any(len(row) != len(x) for row in a):
        raise ValueError("Matrix/vector dimensions disagree")
    return tuple(sum(c * d for c, d in zip(row, x)) for row in a)


def hadd(a: H, b: H) -> H:
    return (a[0] + b[0], a[1] + b[1], a[2] + b[2] + a[0] * b[1])


def hpow(a: H, n: int) -> H:
    integer(n)
    return (n * a[0], n * a[1], n * a[2] + choose2(n) * a[0] * a[1])


@dataclass(frozen=True)
class Element:
    h: tuple[H, ...]
    z: Vector

    def __mul__(self, other: Element) -> Element:
        if len(self.h) != len(other.h) or len(self.z) != len(other.z):
            raise ValueError("Ambient groups disagree")
        return Element(tuple(hadd(a, b) for a, b in zip(self.h, other.h)),
                       tuple(a + b for a, b in zip(self.z, other.z)))

    def power(self, n: int) -> Element:
        integer(n)
        return Element(tuple(hpow(a, n) for a in self.h),
                       tuple(n * a for a in self.z))

    def to_json(self) -> dict:
        return {"h": [list(a) for a in self.h], "z": list(self.z)}

    @classmethod
    def identity(cls, N: int, m: int) -> Element:
        return cls(((0, 0, 0),) * N, (0,) * m)


@dataclass(frozen=True)
class QuadraticRow:
    constant: int
    linear: Vector
    diagonal: Vector
    cross: tuple[tuple[int, int, int], ...] = ()

    def __post_init__(self) -> None:
        integer(self.constant)
        linear = vector(self.linear)
        diagonal = vector(self.diagonal, len(linear))
        cross = tuple(tuple(term) for term in self.cross)
        seen = set()
        for i, j, a in cross:
            integer(i); integer(j); integer(a)
            if not 0 <= i < j < len(self.linear) or (i, j) in seen:
                raise ValueError("Cross pairs must be distinct and satisfy 0 <= i < j < n")
            seen.add((i, j))
        # Snapshot accepted containers so a frozen row cannot retain caller aliases.
        object.__setattr__(self, "linear", linear)
        object.__setattr__(self, "diagonal", diagonal)
        object.__setattr__(self, "cross", cross)

    def evaluate(self, x: Sequence[int]) -> int:
        x = vector(x, len(self.linear))
        return (self.constant + sum(a * b for a, b in zip(self.linear, x))
                + sum(a * b * b for a, b in zip(self.diagonal, x))
                + sum(a * x[i] * x[j] for i, j, a in self.cross))

    def to_json(self) -> dict:
        return {"constant": self.constant, "linear": list(self.linear),
                "diagonal": list(self.diagonal), "cross": [list(t) for t in self.cross]}


@dataclass(frozen=True)
class Compiled:
    n: int
    rows: tuple[QuadraticRow, ...]
    L: Matrix
    C: Matrix
    D: Matrix
    c: Vector

    @property
    def N(self) -> int:
        return len(self.L)

    @property
    def m(self) -> int:
        return len(self.rows)

    def evaluate(self, x: Sequence[int]) -> Vector:
        x = vector(x, self.n)
        return tuple(row.evaluate(x) for row in self.rows)

    def phase_a(self, x: Sequence[int], u: Sequence[int]) -> Element:
        x, u = vector(x, self.n), vector(u, self.N)
        a = matvec(self.L, x)
        dx, cu = matvec(self.D, x), matvec(self.C, u)
        return Element(tuple((p, 0, -v) for p, v in zip(a, u)),
                       tuple(p + q for p, q in zip(dx, cu)))

    def phase_b(self, y: Sequence[int]) -> Element:
        a = matvec(self.L, vector(y, self.n))
        return Element(tuple((0, p, 0) for p in a), (0,) * self.m)

    def phase_t(self, r: Sequence[int]) -> Element:
        r = vector(r, self.N)
        return Element(tuple((-p, -p, choose2(p)) for p in r), (0,) * self.m)

    def target(self, t: Sequence[int]) -> Element:
        t = vector(t, self.m)
        return Element(((0, 0, 0),) * self.N,
                       tuple(v - c for v, c in zip(t, self.c)))

    def canonical(self, x: Sequence[int]) -> tuple[Element, Element, Element]:
        x = vector(x, self.n)
        r = matvec(self.L, x)
        u = tuple(choose2(v) for v in r)
        return self.phase_a(x, u), self.phase_b(x), self.phase_t(r)

    def product(self, x, u, y, r) -> Element:
        return self.phase_a(x, u) * self.phase_b(y) * self.phase_t(r)

    def quartic(self, t, x, u, y, r) -> int:
        """Integer SOS polynomial of degree <= 4, without extra variables."""
        t, x, u = vector(t, self.m), vector(x, self.n), vector(u, self.N)
        y, r = vector(y, self.n), vector(r, self.N)
        a, b = matvec(self.L, x), matvec(self.L, y)
        dx, cu = matvec(self.D, x), matvec(self.C, u)
        ans = 0
        for av, bv, uv, rv in zip(a, b, u, r):
            central = 2 * uv - 2 * av * (bv - rv) - rv * (rv - 1)
            ans += (av - rv)**2 + (bv - rv)**2 + central**2
        return ans + sum((p + q - (v - c))**2
                         for p, q, v, c in zip(dx, cu, t, self.c))

    def bases(self) -> tuple[tuple[Element, ...], ...]:
        ex = [tuple(int(i == j) for i in range(self.n)) for j in range(self.n)]
        eu = [tuple(int(i == j) for i in range(self.N)) for j in range(self.N)]
        zx, zu = (0,) * self.n, (0,) * self.N
        A = tuple(self.phase_a(x, zu) for x in ex) + tuple(self.phase_a(zx, u) for u in eu)
        B = tuple(self.phase_b(y) for y in ex)
        T = tuple(self.phase_t(r) for r in eu)
        return A, B, T

    def to_json(self) -> dict:
        return {"ambient": {"heisenberg_factors": self.N, "abelian_factors": self.m},
                "ranks": [self.n + self.N, self.n, self.N],
                "L": self.L, "C": self.C, "D": self.D, "c": self.c,
                "input": {"n": self.n, "rows": [row.to_json() for row in self.rows]},
                "bases": [[g.to_json() for g in basis] for basis in self.bases()],
                "target_convention": "(identity in H^N, t-c in Z^m)",
                "domains": "All integer exponents for subgroups; all nonnegative for monoids"}


def compile_quadratics(n: int, rows: Sequence[QuadraticRow]) -> Compiled:
    integer(n)
    if n < 1 or not rows:
        raise ValueError("Require n >= 1 and at least one equation")
    rows = tuple(rows)
    if any(len(row.linear) != n for row in rows):
        raise ValueError("All rows must have n variables")
    pairs = sorted({(i, j) for row in rows for i, j, a in row.cross if a})
    L = tuple(tuple(int(i == j) for i in range(n)) for j in range(n))
    L += tuple(tuple(int(k == i or k == j) for k in range(n)) for i, j in pairs)
    C, D = [], []
    for row in rows:
        cross = {(i, j): a for i, j, a in row.cross}
        ci = [2 * a for a in row.diagonal]
        for i, j, a in row.cross:
            ci[i] -= a
            ci[j] -= a
        C.append(tuple(ci + [cross.get(p, 0) for p in pairs]))
        D.append(tuple(a + b for a, b in zip(row.linear, row.diagonal)))
    return Compiled(n, rows, L, tuple(C), tuple(D), tuple(r.constant for r in rows))


def from_json(spec: dict) -> Compiled:
    n = integer(spec["n"])
    rows = tuple(QuadraticRow(integer(row["constant"]), vector(row["linear"], n),
                              vector(row["diagonal"], n),
                              tuple(tuple(t) for t in row.get("cross", [])))
                 for row in spec["rows"])
    return compile_quadratics(n, rows)


def circuit_system(n_inputs: int, gates: Sequence[tuple], pins: Sequence[int]) -> Compiled:
    """Flatten an acyclic arithmetic circuit, then compile its quadratic system.

    Wires 0..n_inputs-1 are free input/witness wires. Gate k creates wire
    n_inputs+k. Gates: ('const', integer), ('add', i, j), ('sub', i, j),
    ('mul', i, j), with i,j earlier wires. Each gate gives residual zero.
    Final rows are the requested wire pins, whose RHS is externally supplied.
    Thus target = [0]*len(gates) + [desired value of each pinned wire].
    Integer circuits use all operations; natural circuits should use only
    const >= 0, add, mul. This routine does not itself impose wire domains.
    """
    integer(n_inputs)
    if n_inputs < 1:
        raise ValueError("Require at least one free wire")
    n = n_inputs + len(gates)
    rows = []
    for k, gate in enumerate(gates):
        out = n_inputs + k
        lin, diag, cross, c = [0] * n, [0] * n, [], 0
        lin[out] = 1
        if gate[0] == "const" and len(gate) == 2:
            c = -integer(gate[1])
        elif gate[0] in {"add", "sub", "mul"} and len(gate) == 3:
            i, j = integer(gate[1]), integer(gate[2])
            if not (0 <= i < out and 0 <= j < out):
                raise ValueError("A gate must use earlier wires")
            if gate[0] in {"add", "sub"}:
                lin[i] -= 1
                lin[j] += 1 if gate[0] == "sub" else -1
            elif i == j:
                diag[i] -= 1
            else:
                cross = [(min(i, j), max(i, j), -1)]
        else:
            raise ValueError(f"Invalid gate {gate!r}")
        rows.append(QuadraticRow(c, tuple(lin), tuple(diag), tuple(cross)))
    for i in pins:
        integer(i)
        if not 0 <= i < n:
            raise ValueError("Pinned wire is out of range")
        rows.append(QuadraticRow(0, tuple(int(k == i) for k in range(n)), (0,) * n))
    return compile_quadratics(n, rows)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("spec", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    try:
        obj = from_json(json.loads(args.spec.read_text(encoding="utf-8")))
        args.output.write_text(json.dumps(obj.to_json(), indent=2) + "\n", encoding="utf-8")
    except (KeyError, TypeError, ValueError, OSError) as exc:
        parser.error(str(exc))


if __name__ == "__main__":
    main()

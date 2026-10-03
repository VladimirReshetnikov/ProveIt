#!/usr/bin/env python3
"""Exact arithmetic van Kampen certificate compilers.

All existential variables range over Z.  These are area/shape-indexed
families, NOT a fixed-arity universal Diophantine equation.  SymPy is used
only by the symbolic compiler; integer evaluation and Sanov decoding use
Python's exact integers.  See the accompanying article for proofs.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Iterable, Sequence, Mapping
import json
from pathlib import Path

Mat = tuple[int, int, int, int]
I: Mat = (1, 0, 0, 1)
A: Mat = (1, 2, 0, 1)
B: Mat = (1, 0, 2, 1)



def _integer_vector(values, length: int, label: str) -> tuple[int, ...]:
    if type(values) not in (tuple, list) or len(values) != length:
        raise ValueError(f"{label} requires exactly {length} integer entries")
    if any(type(value) is not int for value in values):
        raise ValueError(f"{label} entries must be exact integers, not floats or Booleans")
    return tuple(values)


def mul(x: Mat, y: Mat) -> Mat:
    a, b, c, d = x
    e, f, g, h = y
    return (a*e+b*g, a*f+b*h, c*e+d*g, c*f+d*h)


def sub(x: Mat, y: Mat) -> Mat:
    return tuple(a-b for a, b in zip(x, y))  # type: ignore[return-value]


def det(x: Mat) -> int:
    return x[0]*x[3]-x[1]*x[2]


def inverse(x: Mat) -> Mat:
    if det(x) != 1:
        raise ValueError("inverse requires determinant one")
    return (x[3], -x[1], -x[2], x[0])


def power(x: Mat, n: int) -> Mat:
    if n < 0:
        return power(inverse(x), -n)
    out = I
    while n:
        if n & 1:
            out = mul(out, x)
        x = mul(x, x)
        n >>= 1
    return out


LETTERS = {"a": A, "A": inverse(A), "b": B, "B": inverse(B)}


def evaluate_word(word: str) -> Mat:
    out = I
    for letter in word:
        if letter not in LETTERS:
            raise ValueError("words must use a,A,b,B (uppercase means inverse)")
        out = mul(out, LETTERS[letter])
    return out


def inverse_word(word: str) -> str:
    if any(c not in LETTERS for c in word):
        raise ValueError("invalid word")
    return word[::-1].swapcase()


def freely_reduce(word: str) -> str:
    stack: list[str] = []
    for c in word:
        if c not in LETTERS:
            raise ValueError("invalid word")
        if stack and stack[-1] == c.swapcase():
            stack.pop()
        else:
            stack.append(c)
    return "".join(stack)


def conjugate(u: Mat, x: Mat) -> Mat:
    return mul(mul(u, x), inverse(u))


def chart(c: Sequence[int]) -> Mat:
    x, y, z, t = _integer_vector(c, 4, "chart")
    return (1+4*x, 2*y, 2*z, 1+4*t)


def chart_residual(c: Sequence[int]) -> int:
    x, y, z, t = _integer_vector(c, 4, "chart")
    return x+t+4*x*t-y*z


def unchart(u: Mat) -> tuple[int, int, int, int]:
    a, b, c, d = _integer_vector(u, 4, "Sanov matrix")
    if det((a, b, c, d)) != 1 or (a-1) % 4 or b % 2 or c % 2 or (d-1) % 4:
        raise ValueError("matrix is not in the Sanov chart")
    return ((a-1)//4, b//2, c//2, (d-1)//4)


def nearest(n: int, d: int) -> int:
    """Nearest integer to n/d; ties rounded to the upper integer."""
    if not d:
        raise ZeroDivisionError
    if d < 0:
        n, d = -n, -d
    q, r = divmod(n, d)
    return q + int(2*r >= d)


def decode_sanov(u: Mat) -> list[tuple[str, int]]:
    """Return compressed A/B syllables whose product is u.

    No expansion of large powers into strings is performed.  This is the
    even-Euclidean descent proved in the article, not a breadth-first search.
    """
    unchart(u)
    syllables: list[tuple[str, int]] = []
    v = u
    while v[2] != 0:
        before = max(abs(v[0]), abs(v[2]))
        if abs(v[0]) > abs(v[2]):
            k = nearest(v[0], 2*v[2])
            v = mul(power(A, -k), v)
            syllables.append(("a", k))
        else:
            k = nearest(v[2], 2*v[0])
            v = mul(power(B, -k), v)
            syllables.append(("b", k))
        if max(abs(v[0]), abs(v[2])) >= before:
            raise AssertionError("descent invariant failed")
    if v[0] != 1 or v[3] != 1 or v[1] % 2:
        raise AssertionError("invalid terminal matrix")
    if v[1]:
        syllables.append(("a", v[1]//2))
    return syllables


def evaluate_syllables(syllables: Iterable[tuple[str, int]]) -> Mat:
    out = I
    for g, k in syllables:
        if g not in ("a", "b"):
            raise ValueError("syllable generator must be a or b")
        out = mul(out, power(A if g == "a" else B, k))
    return out


def relator_table(relators: Sequence[str]) -> list[Mat]:
    table = [I]
    for r in relators:
        value = evaluate_word(r)
        table.extend((value, inverse(value)))
    return table


@dataclass
class BudgetWitness:
    charts: list[tuple[int, int, int, int]]
    selectors: list[list[int]]
    intermediates: list[Mat]  # P_1,...,P_{m-1}
    products: list[Mat]       # V_1,...,V_m
    boundary: Mat


def make_budget_witness(relators: Sequence[str], labels: Sequence[int],
                        conjugators: Sequence[Mat]) -> BudgetWitness:
    if len(labels) != len(conjugators):
        raise ValueError("one conjugator is required per label")
    table = relator_table(relators)
    us, es, ps, vs = [], [], [], []
    p = I
    for label, u in zip(labels, conjugators):
        if type(label) is not int or not 0 <= label < len(table):
            raise ValueError("relator label out of range")
        us.append(unchart(u))
        es.append([int(j == label) for j in range(len(table))])
        vs.append(mul(p, u))
        p = mul(p, conjugate(u, table[label]))
        ps.append(p)
    return BudgetWitness(us, es, ps[:-1], vs, p)


def budget_residuals(relators: Sequence[str], witness: BudgetWitness) -> list[int]:
    """Direct numerical implementation, separate from the symbolic compiler."""
    table = relator_table(relators)
    if type(witness) is not BudgetWitness:
        raise ValueError("a BudgetWitness is required")
    arrays = (witness.charts, witness.selectors, witness.products, witness.intermediates)
    if any(type(values) is not list for values in arrays):
        raise ValueError("witness arrays must be lists")
    boundary = _integer_vector(witness.boundary, 4, "boundary matrix")
    m = len(witness.charts)
    if (len(witness.selectors) != m or len(witness.products) != m
            or len(witness.intermediates) != max(m-1, 0)):
        raise ValueError("inconsistent witness dimensions")
    for coords in witness.charts:
        _integer_vector(coords, 4, "chart")
    for selectors in witness.selectors:
        _integer_vector(selectors, len(table), "selector vector")
    for matrix in witness.products + witness.intermediates:
        _integer_vector(matrix, 4, "witness matrix")
    if not m:
        return list(sub(boundary, I))
    ps = [I] + witness.intermediates + [witness.boundary]
    residuals: list[int] = []
    for i in range(m):
        c = witness.charts[i]
        u, v, e = chart(c), witness.products[i], witness.selectors[i]
        if len(e) != len(table):
            raise ValueError("selector dimension mismatch")
        selected = tuple(sum(e[j]*table[j][t] for j in range(len(table)))
                         for t in range(4))
        residuals.append(chart_residual(c))
        residuals.extend(x*(x-1) for x in e)
        residuals.append(sum(e)-1)
        residuals.extend(sub(v, mul(ps[i], u)))
        residuals.extend(sub(mul(v, selected), mul(ps[i+1], u)))
    return residuals


@dataclass
class PolynomialSystem:
    parameters: tuple
    variables: tuple
    residuals: tuple
    metadata: dict

    def polynomial(self, expand: bool = False):
        import sympy as sp
        p = sum(r*r for r in self.residuals)
        return sp.expand(p) if expand else p

    def export(self, path: str | Path) -> None:
        """Sparse JSON for quadratic residuals, with an exact SOS finalizer."""
        import sympy as sp
        if (type(self.parameters) is not tuple or type(self.variables) is not tuple
                or type(self.residuals) is not tuple):
            raise ValueError("polynomial arrays must be tuples")
        names = self.parameters + self.variables
        if (not names or len(set(names)) != len(names)
                or any(type(name) is not sp.Symbol or not name.is_integer for name in names)):
            raise ValueError("distinct integer polynomial symbols required")
        sparse_residuals = []
        for residual in self.residuals:
            expr = sp.sympify(residual)
            if expr.atoms(sp.Float):
                raise ValueError("floating polynomial coefficients are not permitted")
            poly = sp.Poly(expr, *names)
            if any(not coef.is_Integer for coef in poly.coeffs()):
                raise ValueError("every polynomial coefficient must be an exact integer")
            sparse_residuals.append([[list(mon), int(coef)] for mon, coef in poly.terms()])
        data = dict(self.metadata)
        data.update(domain="integers", parameters=[str(s) for s in self.parameters],
                    variables=[str(s) for s in self.variables],
                    finalizer="sum of squares of all listed residuals",
                    residuals=sparse_residuals)
        Path(path).write_text(json.dumps(data, indent=2)+"\n", encoding="utf-8")


def _symbolic_chart(coords):
    import sympy as sp
    x, y, z, t = coords
    return sp.Matrix([[1+4*x, 2*y], [2*z, 1+4*t]]), x+t+4*x*t-y*z


def compile_budget(relators: Sequence[str], m: int) -> PolynomialSystem:
    """Compile the all-label area-at-most-m relation, using (2s+13)m-4 vars."""
    import sympy as sp
    if type(m) is not int or m < 0:
        raise ValueError("area budget must be an exact nonnegative integer")
    w = sp.symbols("w00 w01 w10 w11", integer=True)
    W = sp.Matrix(2, 2, w)
    if m == 0:
        return PolynomialSystem(w, (), tuple(W-sp.eye(2)),
                                {"kind": "budget", "budget": 0, "relators": list(relators)})
    table = [sp.Matrix(2, 2, x) for x in relator_table(relators)]
    q = len(table)
    variables, residuals, us, vs, selectors = [], [], [], [], []
    for i in range(m):
        u = sp.symbols(f"u{i}_x u{i}_y u{i}_z u{i}_t", integer=True)
        v = sp.symbols(f"v{i}_00 v{i}_01 v{i}_10 v{i}_11", integer=True)
        e = sp.symbols(f"e{i}_0:{q}", integer=True)
        variables.extend((*u, *v, *e))
        us.append(_symbolic_chart(u))
        vs.append(sp.Matrix(2, 2, v))
        selectors.append(e)
    ps = [sp.eye(2)]
    for i in range(1, m):
        p = sp.symbols(f"p{i}_00 p{i}_01 p{i}_10 p{i}_11", integer=True)
        variables.extend(p)
        ps.append(sp.Matrix(2, 2, p))
    ps.append(W)
    for i in range(m):
        u, determinant_residual = us[i]
        e, v = selectors[i], vs[i]
        c = sum((e[j]*table[j] for j in range(q)), sp.zeros(2))
        residuals.extend([determinant_residual, *(x*(x-1) for x in e), sum(e)-1])
        residuals.extend(v-ps[i]*u)
        residuals.extend(v*c-ps[i+1]*u)
    return PolynomialSystem(w, tuple(variables), tuple(map(sp.expand, residuals)),
                            {"kind": "budget", "budget": m, "relators": list(relators),
                             "label_order": ["identity"] + [s for r in relators for s in (r, inverse_word(r))]})


def symbolic_budget_assignment(system: PolynomialSystem, witness: BudgetWitness) -> dict:
    values: dict[str, int] = dict(zip(("w00", "w01", "w10", "w11"), witness.boundary))
    for i, c in enumerate(witness.charts):
        values.update({f"u{i}_{name}": val for name, val in zip(("x", "y", "z", "t"), c)})
        values.update({f"v{i}_{name}": val for name, val in zip(("00", "01", "10", "11"), witness.products[i])})
        values.update({f"e{i}_{j}": val for j, val in enumerate(witness.selectors[i])})
    for i, p in enumerate(witness.intermediates, 1):
        values.update({f"p{i}_{name}": val for name, val in zip(("00", "01", "10", "11"), p)})
    return {s: values[str(s)] for s in system.parameters + system.variables}


def compile_itinerary(relator_words: Sequence[str]) -> PolynomialSystem:
    """The list is a fixed itinerary, including signs; empty strings mean I."""
    import sympy as sp
    m = len(relator_words)
    w = sp.symbols("w00 w01 w10 w11", integer=True)
    W = sp.Matrix(2, 2, w)
    if m == 0:
        return PolynomialSystem(w, (), tuple(W-sp.eye(2)), {"kind": "itinerary", "words": []})
    variables, residuals, us = [], [], []
    for i in range(m):
        u = sp.symbols(f"u{i}_x u{i}_y u{i}_z u{i}_t", integer=True)
        variables.extend(u)
        us.append(_symbolic_chart(u))
    ps = [sp.eye(2)]
    for i in range(1, m):
        p = sp.symbols(f"p{i}_00 p{i}_01 p{i}_10 p{i}_11", integer=True)
        variables.extend(p)
        ps.append(sp.Matrix(2, 2, p))
    ps.append(W)
    for i, r in enumerate(relator_words):
        u, eq = us[i]
        residuals.append(eq)
        residuals.extend(ps[i]*u*sp.Matrix(2, 2, evaluate_word(r))-ps[i+1]*u)
    return PolynomialSystem(w, tuple(variables), tuple(map(sp.expand, residuals)),
                            {"kind": "itinerary", "words": list(relator_words)})


@dataclass(frozen=True)
class Node:
    kind: str  # leaf, product, inverse, conjugate, fixed_conjugate
    children: tuple[int, ...] = ()
    word: str = ""     # leaf relator or identity, or constant conjugating word
    matrix: Mat | None = None  # optional supplied Sanov matrix for constant conjugation


def validate_dag(nodes: Sequence[Node], relators: Sequence[str]) -> None:
    if not nodes:
        raise ValueError("a proof DAG must have an output")
    allowed = {""} | {r for w in relators for r in (w, inverse_word(w))}
    arities = {"leaf": 0, "product": 2, "inverse": 1, "conjugate": 1, "fixed_conjugate": 1}
    for i, node in enumerate(nodes):
        if node.kind not in arities or len(node.children) != arities[node.kind]:
            raise ValueError("bad node kind or arity")
        if any(type(j) is not int or j < 0 or j >= i for j in node.children):
            raise ValueError("DAG must be topologically ordered and acyclic")
        if node.kind == "leaf" and node.word not in allowed:
            raise ValueError("leaf is not a specified relator or its inverse")
        if node.kind == "fixed_conjugate":
            unchart(node.matrix if node.matrix is not None else evaluate_word(node.word))
    reachable, todo = set(), [len(nodes)-1]
    while todo:
        i = todo.pop()
        if i not in reachable:
            reachable.add(i)
            todo.extend(nodes[i].children)
    if len(reachable) != len(nodes):
        raise ValueError("every node must be reachable from the output")


def evaluate_dag(nodes: Sequence[Node], relators: Sequence[str],
                 conjugators: Mapping[int, Mat] | None = None) -> tuple[list[Mat], list[int]]:
    validate_dag(nodes, relators)
    conjugators = conjugators or {}
    values, costs = [], []
    for i, n in enumerate(nodes):
        if n.kind == "leaf":
            val, cost = evaluate_word(n.word), int(n.word != "")
        elif n.kind == "product":
            a, b = n.children
            val, cost = mul(values[a], values[b]), costs[a]+costs[b]
        elif n.kind == "inverse":
            a = n.children[0]
            val, cost = inverse(values[a]), costs[a]
        else:
            a = n.children[0]
            u = (conjugators[i] if n.kind == "conjugate" else
                 (n.matrix if n.matrix is not None else evaluate_word(n.word)))
            unchart(u)
            val, cost = conjugate(u, values[a]), costs[a]
        values.append(val)
        costs.append(cost)
    return values, costs


def compile_dag(nodes: Sequence[Node], relators: Sequence[str]) -> PolynomialSystem:
    import sympy as sp
    validate_dag(nodes, relators)
    w = sp.symbols("w00 w01 w10 w11", integer=True)
    W = sp.Matrix(2, 2, w)
    variables, residuals, outputs = [], [], []
    for i, n in enumerate(nodes):
        if n.kind == "leaf":
            z = sp.Matrix(2, 2, evaluate_word(n.word))
            if i == len(nodes)-1:
                residuals.extend(W-z)
        else:
            if i == len(nodes)-1:
                z = W
            else:
                symbols = sp.symbols(f"z{i}_00 z{i}_01 z{i}_10 z{i}_11", integer=True)
                variables.extend(symbols)
                z = sp.Matrix(2, 2, symbols)
            x = outputs[n.children[0]]
            if n.kind == "product":
                residuals.extend(z-x*outputs[n.children[1]])
            elif n.kind == "inverse":
                residuals.extend(z-sp.Matrix([[x[1, 1], -x[0, 1]], [-x[1, 0], x[0, 0]]]))
            else:
                if n.kind == "conjugate":
                    symbols = sp.symbols(f"g{i}_x g{i}_y g{i}_z g{i}_t", integer=True)
                    variables.extend(symbols)
                    u, eq = _symbolic_chart(symbols)
                    residuals.append(eq)
                else:
                    u = sp.Matrix(2, 2, n.matrix if n.matrix is not None else evaluate_word(n.word))
                residuals.extend(z*u-u*x)
        outputs.append(z)
    return PolynomialSystem(w, tuple(variables), tuple(map(sp.expand, residuals)),
                            {"kind": "dag", "node_kinds": [n.kind for n in nodes],
                             "relators": list(relators)})


def symbolic_dag_assignment(system: PolynomialSystem, nodes: Sequence[Node],
                            values: Sequence[Mat], conjugators: Mapping[int, Mat]) -> dict:
    d: dict[str, int] = dict(zip(("w00", "w01", "w10", "w11"), values[-1]))
    for i, (n, value) in enumerate(zip(nodes, values)):
        if n.kind != "leaf" and i != len(nodes)-1:
            d.update({f"z{i}_{s}": v for s, v in zip(("00", "01", "10", "11"), value)})
        if n.kind == "conjugate":
            d.update({f"g{i}_{s}": v for s, v in zip(("x", "y", "z", "t"), unchart(conjugators[i]))})
    return {s: d[str(s)] for s in system.parameters + system.variables}


def grid_dag(k: int, ell: int) -> list[Node]:
    """Optimal product-count proof of [a^(2^k), b^(2^ell)]."""
    if k < 0 or ell < 0:
        raise ValueError("nonnegative exponents required")
    nodes = [Node("leaf", word="abAB")]
    current = 0
    for i in range(k):
        nodes.append(Node("fixed_conjugate", (current,), matrix=power(A, 1 << i)))
        conjugated = len(nodes)-1
        nodes.append(Node("product", (conjugated, current)))
        current = len(nodes)-1
    for j in range(ell):
        nodes.append(Node("fixed_conjugate", (current,), matrix=power(B, 1 << j)))
        conjugated = len(nodes)-1
        nodes.append(Node("product", (current, conjugated)))
        current = len(nodes)-1
    return nodes


def rectangular_matrix(p: int, q: int) -> Mat:
    return (1+4*p*q+16*p*p*q*q, -8*p*p*q, 8*p*q*q, 1-4*p*q)


def main() -> None:
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    b = sub.add_parser("budget", help="export a sparse area-budget polynomial")
    b.add_argument("m", type=int)
    b.add_argument("--relator", action="append", default=None)
    b.add_argument("--output", type=Path, required=True)
    g = sub.add_parser("grid", help="export an optimal dyadic grid DAG polynomial")
    g.add_argument("k", type=int)
    g.add_argument("ell", type=int)
    g.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "budget":
        system = compile_budget(args.relator or ["abAB"], args.m)
    else:
        system = compile_dag(grid_dag(args.k, args.ell), ["abAB"])
    system.export(args.output)
    print(json.dumps({"variables": len(system.variables), "residuals": len(system.residuals),
                      "file": str(args.output)}, indent=2))


if __name__ == "__main__":
    main()

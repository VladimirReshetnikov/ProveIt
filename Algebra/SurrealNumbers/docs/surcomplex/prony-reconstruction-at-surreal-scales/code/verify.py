#!/usr/bin/env python3
"""Exact finite checks for Sharp Moment Reconstruction at Surreal Scales.

Requires Python 3.9+ and SymPy. No network, floating point, or external CAS.
These checks verify concrete finite identities, not the general theorems,
arbitrary Hahn support claims, or novelty. Run from any working directory.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import permutations, product
from pathlib import Path
import sys

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required: python -m pip install sympy") from exc

X, t, h, e = sp.symbols("X t h e")
MESSAGES: list[str] = []
CHECKS = 0


def require(condition: bool, description: str) -> None:
    global CHECKS
    if not condition:
        raise AssertionError(description)
    CHECKS += 1


def eq(lhs: sp.Expr, rhs: sp.Expr, description: str) -> None:
    require(sp.cancel(sp.expand(lhs - rhs)) == 0, description)


def note(message: str) -> None:
    MESSAGES.append(message)
    print(message)


def moments(nodes: list[sp.Expr], weights: list[sp.Expr]) -> list[sp.Expr]:
    if len(nodes) != len(weights) or not nodes:
        raise ValueError("Nodes and weights must have equal positive lengths")
    return [sum(w * a**k for a, w in zip(nodes, weights))
            for k in range(2 * len(nodes))]


def functional(poly: sp.Expr, data: list[sp.Expr]) -> sp.Expr:
    p = sp.Poly(poly, X)
    if p.degree() >= len(data):
        raise ValueError("The polynomial exceeds the available moment degree")
    return sp.expand(sum(p.nth(k) * mk for k, mk in enumerate(data)))


def cofactor_data(nodes: list[sp.Expr]):
    P = sp.prod(X - a for a in nodes).expand()
    Q = [sp.div(P, X-a, X)[0] for a in nodes]
    p = [qi.subs(X, a) for qi, a in zip(Q, nodes)]
    return P, Q, p


def check_hermite(nodes: list[sp.Expr], weights: list[sp.Expr]) -> None:
    n = len(nodes)
    P, Q, p = cofactor_data(nodes)
    Hs, Gs = [], []
    for i, a in enumerate(nodes):
        ell = Q[i] / p[i]
        hi = sp.diff(ell, X).subs(X, a)
        H = sp.expand((1 - 2 * hi * (X-a)) * ell**2)
        G = sp.expand((X-a) * ell**2)
        Hs.append(H)
        Gs.append(G)
        for j, b in enumerate(nodes):
            eq(H.subs(X, b), sp.Integer(i == j), "Hermite value")
            eq(sp.diff(H, X).subs(X, b), 0, "Hermite derivative")
            eq(G.subs(X, b), 0, "Hermite G value")
            eq(sp.diff(G, X).subs(X, b), sp.Integer(i == j), "Hermite G derivative")
    J = sp.Matrix([[a**k for a in nodes] +
                   [0 if k == 0 else weights[i] * k * nodes[i]**(k-1)
                    for i in range(n)] for k in range(2*n)])
    inverse_rows = [[sp.Poly(H, X).nth(k) for k in range(2*n)] for H in Hs]
    inverse_rows += [[sp.Poly(Gs[i], X).nth(k)/weights[i] for k in range(2*n)]
                     for i in range(n)]
    R = sp.Matrix(inverse_rows)
    require(R*J == sp.eye(2*n), "Hermite inverse times Jacobian")
    data = moments(nodes, weights)
    Hankel = sp.Matrix(n, n, lambda r, s: data[r+s])
    determinant = sp.prod(weights) * sp.prod(
        (nodes[j]-nodes[i])**2 for i in range(n) for j in range(i+1, n))
    eq(Hankel.det(), determinant, "Hankel determinant")
    note(f"PASS Hermite inverse and Hankel determinant: n={n}, nodes={nodes}")


def check_cofactor_system(nodes, weights, new_nodes, new_weights) -> None:
    n = len(nodes)
    old_m, new_m = moments(nodes, weights), moments(new_nodes, new_weights)
    error = [new_m[k]-old_m[k] for k in range(2*n)]
    P, Q, p = cofactor_data(nodes)
    Ph, Qh, _ = cofactor_data(new_nodes)
    c = [weights[i]*p[i]**2 for i in range(n)]
    B = sp.Matrix(n, n, lambda i, j: functional(Q[i]*Q[j], error)/c[j])
    g = sp.Matrix([functional(P*qi, error) for qi in Q])
    b = sp.Matrix([(Ph-P).subs(X, nodes[i])/p[i] for i in range(n)])
    u = sp.diag(*c)*b
    require((sp.eye(n)+B)*u == -g, "Exact cofactor correction equation")
    eq(Ph, P + sum(b[i]*Q[i] for i in range(n)), "Cofactor polynomial")
    A = sum(weights[i]*Q[i] for i in range(n))
    Ah = sum(new_weights[i]*Qh[i] for i in range(n))
    D = sp.expand(Ah*P-A*Ph)
    for i in range(n):
        eq(D.subs(X, nodes[i]), -u[i], "Cross numerator at base node")
        eq(functional(Ph*Q[i], new_m), 0, "Perturbed orthogonality")
    truncated = sum(new_m[k]*X**(-k-1) for k in range(2*n))
    expanded = sp.expand(Ph*truncated)
    polynomial_part = sum(term for term in sp.Add.make_args(expanded)
                          if term.as_powers_dict().get(X, 0) >= 0)
    eq(polynomial_part, Ah, "Finite Pade numerator")
    cross_expanded = sp.expand(P*Ph*sum(error[k]*X**(-k-1) for k in range(2*n)))
    cross_part = sum(term for term in sp.Add.make_args(cross_expanded)
                     if term.as_powers_dict().get(X, 0) >= 0)
    eq(cross_part, D, "Cross numerator from moment differences")
    note(f"PASS exact cofactor/Pade/cross-numerator identities: n={n}")


def order_at_zero(expr: sp.Expr, variable: sp.Symbol = t) -> int | sp.Expr:
    expr = sp.cancel(expr)
    if expr == 0:
        return sp.oo
    num, den = sp.fraction(expr)
    def polynomial_order(f):
        return min(monomial[0] for monomial, coeff in sp.Poly(f, variable).terms()
                   if coeff != 0)
    return polynomial_order(num)-polynomial_order(den)


def check_two_nodes() -> None:
    P = X*(X-h)
    Pe = sp.expand(P-e*((X-h)+X)/h**2)
    expected = X**2-(h+2*e/h**2)*X+e/h
    eq(Pe, expected, "Last-moment polynomial")
    eq(sp.discriminant(Pe, X), h**2+4*e**2/h**4, "Two-node discriminant")
    eq(Pe.subs(e, sp.I*h**3/2), (X-h*(1+sp.I)/2)**2, "Boundary collision")
    S = sp.sqrt(1+4*h**2)
    nodes = [(h+2*h**2-h*S)/2, (h+2*h**2+h*S)/2]
    weights = [1+2*h/S, 1-2*h/S]
    expected_m = [2, h, h**2, h**3+h**4]
    for k, m in enumerate(expected_m):
        require(sp.simplify(sum(weights[i]*nodes[i]**k for i in range(2))-m) == 0,
                "Exact radical realization")
    displayed = [h**2-h**3+h**5-2*h**7,
                 h+h**2+h**3-h**5+2*h**7,
                 1+2*h-4*h**3+12*h**5-40*h**7,
                 1-2*h+4*h**3-12*h**5+40*h**7]
    for expr, expected_series in zip(nodes+weights, displayed):
        eq(sp.series(expr, h, 0, 9).removeO(), expected_series,
           "Displayed two-node power series")
    note("PASS symbolic last-moment formula, boundary collision, radicals, and series")


def check_cancellation() -> None:
    symmetric = [-h, sp.Integer(0), h]
    generic = [sp.Integer(0), h, 3*h]
    expected = [[-sp.Rational(3, 2)/h, 0, sp.Rational(3, 2)/h],
                [-sp.Rational(4, 3)/h, sp.Rational(1, 2)/h, sp.Rational(5, 6)/h]]
    for nodes, answer in zip([symmetric, generic], expected):
        for i in range(3):
            hi = sum(1/(nodes[i]-nodes[j]) for j in range(3) if i != j)
            eq(hi, answer[i], "Cancellation depth coefficient")
        P, Q, p = cofactor_data(nodes)
        losses = []
        for i, a in enumerate(nodes):
            ell = Q[i]/p[i]
            hi = sp.diff(ell, X).subs(X, a)
            H = sp.expand((1-2*hi*(X-a))*ell**2)
            vals = [order_at_zero(coeff, h) for coeff in sp.Poly(H, X).all_coeffs()]
            losses.append(-min(vals))
        require(losses == ([5, 4, 5] if nodes == symmetric else [5, 5, 5]),
                "Exact Hermite weight row valuations")
    note("PASS identical separation valuations with different weight row losses")


def check_nonlinear_obstruction() -> None:
    lam = sp.symbols("lam")
    P = X**3-sp.Rational(3, 2)*lam*X**2-X+lam
    A = 3*X**2-sp.Rational(9, 2)*lam*X-1
    data = [sp.Integer(3), sp.Integer(0), sp.Integer(2),
            sp.Integer(0), sp.Integer(2), lam]
    for k in range(3):
        eq(functional(P*X**k, data), 0, "Symmetric nonlinear orthogonality")
    eq(A-sp.diff(P, X), -sp.Rational(3, 2)*lam*X,
       "Exact middle-weight numerator difference")
    eq(P, lam-X*(1-X**2+sp.Rational(3, 2)*lam*X),
       "Middle-root unit equation")
    y = lam-sp.Rational(1, 2)*lam**3
    require(order_at_zero(P.subs(X, y), lam) >= 5, "Middle-root truncated series")
    delta_weight = (A/sp.diff(P, X)-1).subs(X, y)
    eq(sp.series(delta_weight, lam, 0, 3).removeO(), sp.Rational(3, 2)*lam**2,
       "Nonlinear middle-weight leading coefficient")
    note("PASS nonlinear middle-weight obstruction and exact numerator identities")


def check_rank_two() -> None:
    # Integer tuples with lexicographic comparison represent the exponents.
    add = lambda a, b: tuple(x+y for x, y in zip(a, b))
    sub = lambda a, b: tuple(x-y for x, y in zip(a, b))
    mul = lambda k, a: tuple(k*x for x in a)
    alpha = [(0, 0), (0, 1), (0, 0), (0, 2)]
    d = [(1, 1), (1, 1), (0, 2), (0, 0)]
    r = [(1, 0), (1, 0), (0, 1), (0, 0)]
    E = [add(alpha[i], mul(2, d[i])) for i in range(4)]
    theta = max(add(E[i], r[i]) for i in range(4))
    kappa = (3, 4)
    node = [sub(kappa, x) for x in E]
    weight = [sub(sub(kappa, mul(2, d[i])), r[i]) for i in range(4)]
    require(theta == (3, 3), "Rank-two threshold")
    require(node == [(1, 2), (1, 1), (3, 0), (3, 2)], "Rank-two node bounds")
    require(weight == [(0, 2), (0, 2), (3, -1), (3, 4)], "Rank-two weight bounds")
    require(all(weight[i] > alpha[i] for i in range(4)), "Weight leading-term preservation")
    note("PASS rank-two lexicographic threshold and error arithmetic")


def check_graph() -> None:
    # g[target][source]; the negative edge is 1 -> 0.
    g = [[2, -1, 4], [3, 2, 1], [2, 2, 2]]
    lam = [10, 7, 8]
    n = len(g)
    means = []
    for length in range(1, n+1):
        for vertices in permutations(range(n), length):
            cost = sum(g[vertices[(k+1) % length]][vertices[k]] for k in range(length))
            require(cost > 0, "Positive simple cycle")
            means.append(Fraction(cost, length))
    eta = min(means)/2
    zeta = [Fraction(0) for _ in range(n)]
    for _ in range(n-1):
        prev = zeta[:]
        zeta = [min([prev[i]]+[prev[j]+g[i][j]-eta for j in range(n)]) for i in range(n)]
    require(all(g[i][j]+zeta[j]-zeta[i] >= eta for i in range(n) for j in range(n)),
            "Diagonal-scaling potentials")
    rho = lam[:]
    for length in range(1, n):
        for path in permutations(range(n), length+1):
            cost = lam[path[0]]+sum(g[path[k+1]][path[k]] for k in range(length))
            rho[path[-1]] = min(rho[path[-1]], cost)
    require(rho == [6, 7, 8], "Shortest simple path bounds")
    # Check all walks through length 7 as finite corroboration, not a general proof.
    for length in range(8):
        for walk in product(range(n), repeat=length+1):
            cost = lam[walk[0]]+sum(g[walk[k+1]][walk[k]] for k in range(length))
            require(cost >= rho[walk[-1]], "Walk bound after cycle removal")
    B = sp.Matrix(n, n, lambda i, j: t**g[i][j])
    rhs = sp.Matrix([t**l for l in lam])
    u = -(sp.eye(n)+B).inv()*rhs
    actual = [order_at_zero(ui) for ui in u]
    require(all(actual[i] >= rho[i] for i in range(n)), "Exact rational matrix solution bound")
    note(f"PASS graph scaling: eta={eta}, potentials={zeta}, rho={rho}, actual={actual}")


def main() -> int:
    old_log = Path(__file__).resolve().parents[1] / "data" / "verification.txt"
    if old_log.exists():
        old_log.unlink()
    note("Exact finite verification; not a proof of infinite or general claims.")
    note(f"Python {sys.version.split()[0]}; SymPy {sp.__version__}")
    for nodes, weights in [([0], [2]), ([0, 2], [1, 3]),
                           ([-2, 0, 3], [2, -3, 5]),
                           ([-3, -1, 2, 5], [1, 2, -1, 4])]:
        a, w = list(map(sp.Rational, nodes)), list(map(sp.Rational, weights))
        check_hermite(a, w)
        ah = [ai+sp.Rational(i+1, 31) for i, ai in enumerate(a)]
        wh = [wi+sp.Rational(2*i+1, 47) for i, wi in enumerate(w)]
        check_cofactor_system(a, w, ah, wh)
    check_two_nodes()
    check_cancellation()
    check_nonlinear_obstruction()
    check_rank_two()
    check_graph()
    note(f"SUCCESS: {CHECKS} exact assertions passed.")
    destination = Path(__file__).resolve().parents[1] / "data" / "verification.txt"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text("\n".join(MESSAGES)+"\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

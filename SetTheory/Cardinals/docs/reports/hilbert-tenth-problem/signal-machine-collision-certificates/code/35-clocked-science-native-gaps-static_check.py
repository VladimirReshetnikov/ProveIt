#!/usr/bin/env python3
"""Fresh static algebra only; no imports or execution from dependency packets."""
from pathlib import Path
import hashlib
import json
from math import gcd


class Poly:
    """Sparse integer polynomials; monomial is sorted (name, exponent) pairs."""

    def __init__(self, terms):
        self.terms = {m: c for m, c in terms.items() if c}

    @staticmethod
    def const(c):
        return Poly({(): c})

    @staticmethod
    def var(name):
        return Poly({((name, 1),): 1})

    @staticmethod
    def coerce(x):
        return x if isinstance(x, Poly) else Poly.const(x)

    def __add__(self, other):
        out = dict(self.terms)
        for m, c in Poly.coerce(other).terms.items():
            out[m] = out.get(m, 0) + c
        return Poly(out)

    __radd__ = __add__

    def __neg__(self):
        return Poly({m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        return self + -Poly.coerce(other)

    def __rsub__(self, other):
        return Poly.coerce(other) + -self

    def __mul__(self, other):
        out = {}
        for m, c in self.terms.items():
            for n, d in Poly.coerce(other).terms.items():
                powers = dict(m)
                for name, exp in n:
                    powers[name] = powers.get(name, 0) + exp
                mon = tuple(sorted(powers.items()))
                out[mon] = out.get(mon, 0) + c * d
        return Poly(out)

    __rmul__ = __mul__

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        out = Poly.const(1)
        for _ in range(n):
            out = out * self
        return out

    def degree(self):
        return max((sum(e for _, e in m) for m in self.terms), default=-1)

    def support(self):
        return {name for mon in self.terms for name, _ in mon}

    def evaluate(self, values):
        total = 0
        for mon, coeff in self.terms.items():
            term = coeff
            for name, exp in mon:
                term *= values[name] ** exp
            total += term
        return total


class Formula:
    def __init__(self):
        self.inputs = set()
        self.witnesses = set()
        self.residuals = []

    def leaf(self, name, input=False):
        assert name not in self.inputs | self.witnesses
        (self.inputs if input else self.witnesses).add(name)
        return Poly.var(name)

    def add(self, name, residual):
        assert name not in {n for n, _ in self.residuals}
        self.residuals.append((name, Poly.coerce(residual)))

    def polynomial(self):
        return sum((r * r for _, r in self.residuals), Poly.const(0))


DIRECT = "o w M g x_p y_p u_p v_p s_p t_p q_b q_v J_p".split()
NATURAL = "d_wb d_wk d_yk alpha_1 alpha_2 sigma_1 sigma_2 tau_1 tau_2 r_1 r_2".split()


def power(f, prefix, C, output):
    """Literal Section 3; output is one of these module's 26 leaves."""
    before = set(f.witnesses)
    p = {n: f.leaf(output if n == "o" else prefix + n) for n in DIRECT}
    p["alpha"] = f.leaf(prefix + "alpha_plus") + 1
    p["beta"] = f.leaf(prefix + "beta_plus") + 1
    p.update({n: f.leaf(prefix + n + "_plus") - 1 for n in NATURAL})
    o, w, M, g, x, y, u, v, s, t, qb, qv, J = (p[n] for n in DIRECT)
    a, b = p["alpha"], p["beta"]
    dwb, dwk, dyk, a1, a2, s1, s2, t1, t2, r1, r2 = (p[n] for n in NATURAL)
    rs = [
        x*x - 1 - (a*a-1)*y*y,
        u*u - 1 - (a*a-1)*v*v,
        s*s - 1 - (b*b-1)*t*t,
        b - 1 - 4*y*qb,
        b + u*a1 - a - u*a2,
        v - y*y*qv,
        s + u*s1 - x - u*s2,
        t + 4*y*t1 - C - 4*y*t2,
        y - C - dyk,
        w - 2 - dwb,
        w - C - dwk,
        M - 2*o - J,
        a*a - 1 - ((w+1)*(w+1)-1)*(w*g)*(w*g),
        4*a - M - 5,
        x + M*r1 - y*(a-2) - 2*o - M*r2,
    ]
    assert len(f.witnesses - before) == 26
    assert len(rs) == 15
    for j, residual in enumerate(rs, 1):
        f.add(prefix + "R" + str(j), residual)
    assert [r.degree() for r in rs] == [4, 4, 4, 2, 2, 3, 2, 2, 1, 1, 1, 1, 6, 1, 2]
    return o


# Each literal tuple is (source, target, A change, B change, zero-tested counter).
# These are fixed instruction data, not a saved or inferred execution schedule.
EDGES = [
    (0, 1, 1, 0, None),
    (1, 4, 0, 0, "A"),
    (1, 2, -1, 0, None),
    (2, 3, 0, 1, None),
    (3, 4, 0, 0, "B"),
    (3, 4, 0, -1, None),
    (4, 4, 0, 0, None),
]


def build(T, edges=EDGES, initial=0, halt=4, exact=False):
    assert T >= 0
    f = Formula()
    g1, g2, g3 = [f.leaf("g" + str(j), input=True) for j in (1, 2, 3)]
    D = g1 + g2 + g3
    A, B = f.leaf("A"), f.leaf("B")
    P, Q = power(f, "pa_", A, "P"), power(f, "pb_", B, "Q")
    f.add("gap1", (20*g1-D)*P - 2*D)
    f.add("gap3", (20*g3-D)*Q - 2*D)
    if T == 0:
        f.add("trace_constant", initial-halt)
        return f
    selectors = []
    AA, BB = [A], [B]
    for t in range(T):
        ss = []
        for e in range(len(edges)):
            w = f.leaf(f"w_{t}_{e}")
            ss.append(w-1)
            f.add(f"selector_{t}_{e}", (w-1)*(w-2))
        selectors.append(ss)
        AA.append(f.leaf(f"A_{t+1}"))
        BB.append(f.leaf(f"B_{t+1}"))
    for t, ss in enumerate(selectors):
        f.add(f"one_{t}", sum(ss)-1)
        f.add(f"update_A_{t}", AA[t+1]-AA[t]-sum(edge[2]*s for edge, s in zip(edges, ss)))
        f.add(f"update_B_{t}", BB[t+1]-BB[t]-sum(edge[3]*s for edge, s in zip(edges, ss)))
        for e, edge in enumerate(edges):
            if edge[4] is not None:
                counter = AA[t] if edge[4] == "A" else BB[t]
                f.add(f"zero_{t}_{e}", ss[e]*(counter-1))
    f.add("initial", sum(edge[0]*s for edge, s in zip(edges, selectors[0]))-initial)
    for t in range(T-1):
        f.add(f"link_{t}", sum(edge[1]*s for edge, s in zip(edges, selectors[t]))
              - sum(edge[0]*s for edge, s in zip(edges, selectors[t+1])))
    f.add("final", sum(edge[1]*s for edge, s in zip(edges, selectors[-1]))-halt)
    if exact:
        halt_edges = [e for e, edge in enumerate(edges) if edge[:4] == (halt, halt, 0, 0)]
        assert len(halt_edges) == 1
        f.add("early_halt", sum(ss[halt_edges[0]] for ss in selectors))
    return f


def power_zero_values(prefix, output):
    values = dict(zip(DIRECT, [1, 2, 63, 3, 17, 1, 577, 34, 17, 1, 4, 34, 61]))
    result = {(output if n == "o" else prefix+n): value for n, value in values.items()}
    result.update({prefix+"alpha_plus": 16, prefix+"beta_plus": 16})
    result.update({prefix+n+"_plus": 2 if n == "d_wk" else 1 for n in NATURAL})
    return result


def assignment(f, selected, counters, scale=1):
    values = {"g1": 3*scale, "g2": 14*scale, "g3": 3*scale, "A": 1, "B": 1}
    values.update(power_zero_values("pa_", "P"))
    values.update(power_zero_values("pb_", "Q"))
    for t, e_selected in enumerate(selected):
        for e in range(len(EDGES)):
            values[f"w_{t}_{e}"] = 2 if e == e_selected else 1
        values[f"A_{t+1}"], values[f"B_{t+1}"] = counters[t]
    assert set(values) == f.inputs | f.witnesses
    assert min(values.values()) >= 1
    return values


def residual_evaluation(f, values):
    return {name: r.evaluate(values) for name, r in f.residuals}


def decoding(gaps):
    D = sum(gaps)
    out = []
    for gap in (gaps[0], gaps[2]):
        den = 20*gap-D
        if den <= 0 or (2*D) % den:
            return None
        power = (2*D)//den
        if power <= 0 or power & (power-1):
            return None
        out.append(power.bit_length()-1)
    return tuple(out)


def checks():
    ledger = []
    for label, edges, initial, halt in [("both_guards", EDGES, 0, 4), ("halt_only", [(0, 0, 0, 0, None)], 0, 0)]:
        for T in (0, 1, 2, 4, 5):
            for exact in (False, True):
                f = build(T, edges, initial, halt, exact)
                poly = f.polynomial()
                E, Z = len(edges), sum(e[4] is not None for e in edges)
                expected_residuals = T*(E+Z+4)+33+int(exact and T > 0)
                assert len(f.inputs) == 3
                assert len(f.witnesses) == T*(E+2)+54
                assert len(f.residuals) == expected_residuals
                assert poly.support() == f.inputs | f.witnesses
                assert poly.degree() == 12
                top = {m: c for m, c in poly.terms.items() if sum(e for _, e in m) == 12}
                expected_top = {tuple(sorted(((p+"w", 8), (p+"g", 4)))): 1 for p in ("pa_", "pb_")}
                assert top == expected_top
                ledger.append({"graph": label, "T": T, "exact": exact, "inputs": 3,
                               "witnesses": len(f.witnesses), "residuals": len(f.residuals),
                               "degree": 12, "expanded_monomials": len(poly.terms),
                               "top_degree_monomials": ["pa_w^8*pa_g^4", "pb_w^8*pb_g^4"]})

    # Declared manually: increment A, positive-decrement A, increment B,
    # positive-decrement B. No machine interpreter computes this fixture.
    selected = [0, 2, 3, 5]
    counters = [(2, 1), (1, 1), (1, 2), (1, 1)]
    full = build(4)
    values = assignment(full, selected, counters)
    assert not any(residual_evaluation(full, values).values())
    assert full.polynomial().evaluate(values) == 0
    exact4 = build(4, exact=True)
    assert exact4.polynomial().evaluate(values) == 0
    scaled = assignment(full, selected, counters, scale=37)
    assert full.polynomial().evaluate(scaled) == 0
    padded = build(5)
    padded_values = assignment(padded, selected+[6], counters+[(1, 1)])
    assert padded.polynomial().evaluate(padded_values) == 0
    assert build(5, exact=True).polynomial().evaluate(padded_values) == 1
    bad = dict(values)
    bad["A_2"] = 2
    assert full.polynomial().evaluate(bad) > 0
    nonencoded = dict(values)
    nonencoded["g1"] += 1
    assert full.polynomial().evaluate(nonencoded) > 0
    for bump in (1, 2, 10, 10**12):
        altered = dict(values)
        altered["pa_alpha_1_plus"] += bump
        altered["pa_alpha_2_plus"] += bump
        assert full.polynomial().evaluate(altered) == 0

    zero = build(0, initial=4)
    zero_values = assignment(zero, [], [])
    assert zero.polynomial().evaluate(zero_values) == 0
    assert build(0).polynomial().evaluate(zero_values) == 16

    normalization_cases = 0
    gcd_counts = {}
    for a in range(65):
        for b in range(65):
            m = max(a, b)
            U = 2**m+2**(m-a+1)
            W = 2**m+2**(m-b+1)
            V = 20*2**m-U-W
            c = gcd(gcd(U, V), W)
            if m == 0:
                expected = 1
            elif a == b == 1:
                expected = 4
            elif m == 1:
                expected = 2
            else:
                expected = 10 if a % 4 == b % 4 == 3 else 2
            assert c == expected
            primitive = (U//c, V//c, W//c)
            D = sum(primitive)
            assert gcd(gcd(primitive[0], primitive[1]), primitive[2]) == 1
            assert min(primitive) > 0 and max(primitive) == primitive[1]
            assert D == 20*2**m//c
            expected_bits = 5 if m == 0 else (4 if a == b == 1 else (5 if m == 1 else m+(2 if c == 10 else 4)))
            assert D.bit_length() == expected_bits
            assert D.bit_length()-1 <= max(x.bit_length() for x in primitive) <= D.bit_length()
            assert (20*primitive[0]-D)*2**a == 2*D
            assert (20*primitive[2]-D)*2**b == 2*D
            for multiplier in (1, 2, 7, 100):
                scaled = tuple(multiplier*x for x in primitive)
                assert decoding(scaled) == (a, b)
            normalization_cases += 1
            gcd_counts[str(c)] = gcd_counts.get(str(c), 0)+1
    assert decoding((1, 1, 1)) is None
    assert decoding((1, 100, 1)) is None
    assert decoding((3, 14, 3)) == (0, 0)
    assert decoding((1, 8, 1)) == (1, 1)
    assert decoding((1, 14, 1)) == (3, 3)

    return {"status": "passed", "ledger_instances": ledger,
            "complete_positive_fixture": "a=b=0, both guards graph, first halt at 4",
            "checked_variants": ["scaled input", "virtual halt padding", "exact-halt rejection",
                                 "counter corruption", "gap corruption", "quotient-pair nonuniqueness",
                                 "T=0 initial halt and nonhalt"],
            "normalization_counter_range": [0, 64], "normalization_cases": normalization_cases,
            "gcd_distribution": gcd_counts, "scaled_decoding_cases": 4*normalization_cases,
            "power_dependency_executed": False, "physical_simulator_executed": False,
            "author_or_upstream_code_executed": False,
            "limits": "Finite static checks support the written proof; all-exponent POWER uses pinned Pell theorems."}


if __name__ == "__main__":
    evidence = checks()
    evidence["checker_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    target = Path(__file__).resolve().parent / "evidence" / "static_checks.json"
    target.write_text(json.dumps(evidence, indent=2, sort_keys=True)+"\n")
    print(json.dumps({"status": evidence["status"], "ledger_instances": len(evidence["ledger_instances"]),
                      "normalization_cases": evidence["normalization_cases"],
                      "scaled_decoding_cases": evidence["scaled_decoding_cases"],
                      "evidence": str(target)}, sort_keys=True))

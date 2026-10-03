"""Exact self-sizing cellular certificates over N[X]. Python 3.10+, no dependencies.

Polynomial coordinates are formal indeterminates, never floating-point values.
The external horizon in candidate() is only a witness-construction argument;
compile_system() accepts no horizon or stride bound.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from types import MappingProxyType
from typing import Iterable, Mapping

Poly = dict[int, int]
Key = tuple[int, tuple[str, ...]]
Expr = dict[Key, int]


def nat(value: object, label: str) -> int:
    if type(value) is not int or value < 0:
        raise ValueError(f"{label} must be a nonnegative integer (not bool)")
    return value


def clean(p: Mapping[int, int]) -> Poly:
    return {e: c for e, c in p.items() if c}


def add(*polys: Mapping[int, int]) -> Poly:
    out: Poly = {}
    for p in polys:
        for e, c in p.items():
            out[e] = out.get(e, 0) + c
    return clean(out)


def scale(p: Mapping[int, int], c: int) -> Poly:
    return {e: c * a for e, a in p.items() if c * a}


def shift(p: Mapping[int, int], k: int) -> Poly:
    return {e + k: c for e, c in p.items()}


def mul(p: Mapping[int, int], q: Mapping[int, int]) -> Poly:
    out: Poly = {}
    for e, a in p.items():
        for f, b in q.items():
            out[e + f] = out.get(e + f, 0) + a * b
    return clean(out)


def mono(e: int, c: int = 1) -> Poly:
    return {e: c} if c else {}


def rep(k: int, start: int = 0) -> Poly:
    return {e: 1 for e in range(start, start + k)}


def eadd(*expressions: Mapping[Key, int]) -> Expr:
    out: Expr = {}
    for expr in expressions:
        for key, c in expr.items():
            out[key] = out.get(key, 0) + c
    return {key: c for key, c in out.items() if c}


def escale(expr: Mapping[Key, int], c: int) -> Expr:
    return {key: c * a for key, a in expr.items() if c * a}


def eshift(expr: Mapping[Key, int], e: int) -> Expr:
    return {(k + e, names): c for (k, names), c in expr.items()}


def emul(left: Mapping[Key, int], right: Mapping[Key, int]) -> Expr:
    out: Expr = {}
    for (e, names), c in left.items():
        for (f, others), d in right.items():
            key = (e + f, tuple(sorted(names + others)))
            out[key] = out.get(key, 0) + c * d
    return {key: c for key, c in out.items() if c}


def var(name: str) -> Expr:
    return {(0, (name,)): 1}


def const(p: Mapping[int, int]) -> Expr:
    return {(e, ()): c for e, c in p.items() if c}


def evaluate(expr: Mapping[Key, int], witness: Mapping[str, Mapping[int, int]],
             cache: dict[tuple[str, ...], Poly] | None = None) -> Poly:
    if cache is None:
        cache = {(): {0: 1}}
    out: Poly = {}
    for (e, names), c in expr.items():
        if names not in cache:
            p = {0: 1}
            for name in names:
                p = mul(p, witness[name])
                if not p:
                    break
            cache[names] = p
        for j, a in cache[names].items():
            out[j + e] = out.get(j + e, 0) + c * a
    return clean(out)


@dataclass(frozen=True)
class Rule:
    s: int
    table: tuple[int, ...]
    accepting: frozenset[int]

    def __post_init__(self) -> None:
        nat(self.s, "alphabet size")
        if self.s < 2:
            raise ValueError("this implementation requires at least two symbols")
        table = tuple(self.table)
        accepting = frozenset(self.accepting)
        if len(table) != self.s ** 3:
            raise ValueError("rule table must have exactly s**3 entries")
        for a in table:
            nat(a, "rule output")
            if a >= self.s:
                raise ValueError("rule output is outside the alphabet")
        for a in accepting:
            nat(a, "accepting symbol")
            if not 0 < a < self.s:
                raise ValueError("accepting symbols must be nonblank alphabet symbols")
        if table[0] != 0:
            raise ValueError("blank must be quiescent")
        object.__setattr__(self, "table", table)
        object.__setattr__(self, "accepting", accepting)

    def output(self, left: int, centre: int, right: int) -> int:
        return self.table[(left * self.s + centre) * self.s + right]

    @classmethod
    def from_function(cls, s: int, fn, accepting: Iterable[int]) -> "Rule":
        return cls(s, tuple(fn(*triple) for triple in product(range(s), repeat=3)),
                   frozenset(accepting))


def validate_word(rule: Rule, word: Iterable[int]) -> tuple[int, ...]:
    out = tuple(word)
    if not out:
        raise ValueError("input word must be nonempty")
    for a in out:
        nat(a, "input symbol")
        if a >= rule.s:
            raise ValueError("input symbol is outside the alphabet")
    return out


def tile_name(triple: tuple[int, int, int]) -> str:
    return "z_" + "_".join(map(str, triple))


@dataclass(frozen=True)
class System:
    rule: Rule
    word: tuple[int, ...]
    names: tuple[str, ...]
    residuals: Mapping[str, Mapping[Key, int]]
    feature_count: int

    def __post_init__(self) -> None:
        # Freeze a deep copy rather than retaining mutable caller-owned mappings.
        object.__setattr__(self, "residuals", MappingProxyType({
            label: MappingProxyType(dict(expr)) for label, expr in self.residuals.items()
        }))

    def checked_witness(self, witness: Mapping[str, Mapping[int, int]]) -> dict[str, Poly]:
        if set(witness) != set(self.names):
            raise ValueError("witness keys must equal the complete variable interface")
        result: dict[str, Poly] = {}
        for name in self.names:
            p = witness[name]
            for e, c in p.items():
                nat(e, f"exponent in {name}")
                nat(c, f"coefficient in {name}")
            result[name] = clean(p)
        return result

    def evaluate(self, witness: Mapping[str, Mapping[int, int]], *,
                 validate: bool = True) -> dict[str, Poly]:
        w = self.checked_witness(witness) if validate else witness
        cache = {(): {0: 1}}
        return {label: evaluate(expr, w, cache) for label, expr in self.residuals.items()}

    def accepts(self, witness: Mapping[str, Mapping[int, int]]) -> bool:
        return not any(self.evaluate(witness).values())

    def quartic(self) -> Expr:
        out: Expr = {}
        for expr in self.residuals.values():
            out = eadd(out, emul(expr, expr))
        return out


def compile_system(rule: Rule, word: Iterable[int], *,
                   features: Iterable[Iterable[int]] | None = None) -> System:
    """Compile a fixed-template system; no time horizon is an argument.

    Default: one weighted feature a -> a (11 equations).
    features may supply any injective vector code with blank mapped to zero.
    """
    w = validate_word(rule, word)
    s, m = rule.s, len(w)
    if features is None:
        code = tuple((a,) for a in range(s))
    else:
        code = tuple(tuple(v) for v in features)
        if len(code) != s or not code or not code[0]:
            raise ValueError("features must give a nonempty vector for each symbol")
        d = len(code[0])
        if any(len(v) != d for v in code):
            raise ValueError("feature vectors must have a common length")
        for v in code:
            for a in v:
                nat(a, "feature coordinate")
        if any(code[0]) or len(set(code)) != s:
            raise ValueError("features must be injective and send blank to zero")
    triples = list(product(range(s), repeat=3))
    z = {triple: var(tile_name(triple)) for triple in triples}
    terminal = {a: var(f"t_{a}") for a in range(s)}
    names = tuple(tile_name(t) for t in triples) + tuple(f"t_{a}" for a in range(s))
    names += ("d", "q", "b", "v", "j", "stride", "stride_prefix")
    D, Q, B, V, J, S, E = map(var, names[-7:])
    H, K = eadd(*z.values()), eadd(*terminal.values())
    G = eadd(V, B, Q, D)
    cf = eadd(*(z[t] for t in triples if t[1] in rule.accepting))
    tf = eadd(*(terminal[a] for a in rule.accepting))
    rows: dict[str, Expr] = {
        "right_clock": eadd(D, Q, escale(const(mono(m + 1)), -1),
                             escale(eshift(emul(S, Q), 2), -1)),
        "vertical_clock": eadd(B, V, const({0: -1}), escale(emul(S, V), -1)),
        "source_shape": eadd(eshift(H, 1), V, escale(H, -1), escale(eshift(Q, 1), -1)),
        "terminal_shape": eadd(H, K, escale(const(rep(m, 1)), -1),
                                escale(eshift(emul(S, H), 1), -1), escale(G, -1)),
    }
    for k in range(len(code[0])):
        L = eadd(*(escale(z[t], code[t[0]][k]) for t in triples))
        C = eadd(*(escale(z[t], code[t[1]][k]) for t in triples))
        R = eadd(*(escale(z[t], code[t[2]][k]) for t in triples))
        O = eadd(*(escale(z[t], code[rule.output(*t)][k]) for t in triples))
        T = eadd(*(escale(terminal[a], code[a][k]) for a in range(s)))
        I = const({j: code[a][k] for j, a in enumerate(w) if code[a][k]})
        rows[f"left_feature_{k}"] = eadd(eshift(C, 1), escale(L, -1))
        rows[f"right_feature_{k}"] = eadd(eshift(R, 1), escale(C, -1))
        rows[f"vertical_feature_{k}"] = eadd(C, T, escale(eshift(I, 1), -1),
                                                   escale(eshift(emul(S, O), 1), -1))
    rows["no_earlier_acceptance"] = cf
    rows["singleton_terminal"] = eadd(tf, J, escale(B, -1), escale(eshift(J, 1), -1))
    rows["positive_stride"] = eadd(S, E, const({1: -1}), escale(eshift(E, 1), -1))
    rows["calibration"] = eadd(emul(S, B), escale(eshift(D, 1), -1))
    return System(rule, w, names, rows, len(code[0]))


def configurations(rule: Rule, word: Iterable[int], horizon: int) -> list[dict[int, int]]:
    nat(horizon, "horizon")
    w = validate_word(rule, word)
    states = [{i: a for i, a in enumerate(w) if a}]
    for t in range(horizon):
        old = states[-1]
        states.append({i: a for i in range(-t - 1, len(w) + t + 1)
                       if (a := rule.output(old.get(i - 1, 0), old.get(i, 0), old.get(i + 1, 0)))})
    return states


def first_singleton_at(rule: Rule, word: Iterable[int], horizon: int) -> bool:
    states = configurations(rule, word, horizon)
    counts = [sum(a in rule.accepting for a in state.values()) for state in states]
    return all(c == 0 for c in counts[:-1]) and counts[-1] == 1


def candidate(system: System, horizon: int, *, width: int | None = None) -> dict[str, Poly]:
    """Construct a candidate, even for a nonaccepting or non-first horizon.

    A supplied alternative width is useful for testing the calibration equation.
    It does not change the compiled system.
    """
    nat(horizon, "horizon")
    m, h, rule = len(system.word), horizon, system.rule
    W = m + 2 * h + 2 if width is None else nat(width, "width")
    if W < 1:
        raise ValueError("candidate width must be positive")
    states = configurations(rule, system.word, h)
    out: dict[str, Poly] = {name: {} for name in system.names}
    def put(name: str, e: int) -> None:
        out[name][e] = out[name].get(e, 0) + 1
    for t in range(h):
        state = states[t]
        for j in range(m + 2 * t + 2):
            i = j - t - 1
            triple = (state.get(i - 1, 0), state.get(i, 0), state.get(i + 1, 0))
            put(tile_name(triple), W * t + j)
    for j in range(m + 2 * h + 2):
        put(f"t_{states[h].get(j - h - 1, 0)}", W * h + j)
    out["d"] = mono(W * h + m + 2 * h + 1)
    out["q"] = {W * t + m + 2 * t + 1: 1 for t in range(h)}
    out["b"] = mono(W * h)
    out["v"] = {W * t: 1 for t in range(h)}
    out["stride"] = mono(W)
    out["stride_prefix"] = rep(W - 1, 1)
    accepting = sorted(i for i, a in states[h].items() if a in rule.accepting)
    out["j"] = rep(accepting[0] + h + 1, W * h) if accepting else {}
    return out


def example_rule() -> Rule:
    def f(left: int, centre: int, right: int) -> int:
        if centre == 3:
            return 3
        if centre == 2:
            return 3 if left == 1 else 2
        if centre == 1:
            return 0
        return 1 if left == 1 else 0
    return Rule.from_function(4, f, {3})


def expression_json(expr: Mapping[Key, int]) -> list[dict]:
    return [{"x_power": e, "variables": list(names), "coefficient": c}
            for (e, names), c in sorted(expr.items())]


def polynomial_json(p: Mapping[int, int]) -> list[list[int]]:
    return [[e, c] for e, c in sorted(p.items()) if c]

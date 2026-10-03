"""Exact compiler for coercive Green-function certificates.

Python >= 3.10, standard library only. No halting oracle is used.
A horizon failure means only that the finite search did not reach a halt.
The universal-machine existence theorem is in the article; this module accepts
explicit finite instruction tables and does not ship a minimal universal table.
"""
from __future__ import annotations
from dataclasses import dataclass, field
from fractions import Fraction
from collections import defaultdict
from typing import Mapping, Sequence
import argparse
import json
from pathlib import Path


def exact_nat(value: object, name: str) -> int:
    if type(value) is not int or value < 0:
        raise ValueError(f"{name} must be an exact nonnegative Python int")
    return value


def exact_int(value: object, name: str) -> int:
    if type(value) is not int:
        raise ValueError(f"{name} must be an exact Python int")
    return value


def alpha_check(alpha: object) -> int:
    alpha = exact_nat(alpha, "alpha")
    if alpha < 3:
        raise ValueError("alpha must be at least 3")
    return alpha


@dataclass(frozen=True, slots=True, order=True)
class Config:
    state: int
    c0: int
    c1: int
    history: int = 0

    def __post_init__(self) -> None:
        for name in ("state", "c0", "c1", "history"):
            exact_nat(getattr(self, name), name)

    def as_list(self) -> list[int]:
        return [self.state, self.c0, self.c1, self.history]


@dataclass(frozen=True, slots=True)
class Branch:
    source: int
    target: int
    kind: str
    register: int
    tag: int


@dataclass(frozen=True, slots=True)
class Program:
    """Instructions: ('inc', register, target),
    ('test', register, positive_target, zero_target), or ('halt',).
    Constructor defensively freezes nested input and validates every scalar.
    """
    instructions: tuple[tuple, ...]
    branches: tuple[Branch, ...] = field(init=False)
    base: int = field(init=False)

    def __post_init__(self) -> None:
        raw = self.instructions
        if not isinstance(raw, (tuple, list)) or not raw:
            raise ValueError("instructions must be a nonempty tuple/list")
        n = len(raw)
        frozen = []
        branches = []
        for state, ins in enumerate(raw):
            if not isinstance(ins, (tuple, list)) or not ins:
                raise ValueError("each instruction must be a nonempty tuple/list")
            op = ins[0]
            if type(op) is not str or op not in ("inc", "test", "halt"):
                raise ValueError("unknown instruction")
            size = {"inc": 3, "test": 4, "halt": 1}[op]
            if len(ins) != size:
                raise ValueError(f"wrong arity for {op}")
            if op != "halt":
                reg = exact_nat(ins[1], "register")
                if reg not in (0, 1):
                    raise ValueError("register must be 0 or 1")
                for target in ins[2:]:
                    if exact_nat(target, "target") >= n:
                        raise ValueError("target outside instruction table")
                kinds = ("inc",) if op == "inc" else ("dec", "zero")
                for kind, target in zip(kinds, ins[2:]):
                    branches.append(Branch(state, target, kind, reg, len(branches) + 1))
            frozen.append(tuple(ins))
        object.__setattr__(self, "instructions", tuple(frozen))
        object.__setattr__(self, "branches", tuple(branches))
        object.__setattr__(self, "base", max(2, len(branches) + 1))

    def validate_config(self, c: Config, root: bool = False) -> None:
        if not isinstance(c, Config) or c.state >= len(self.instructions):
            raise ValueError("configuration has an invalid state")
        if root and c.history != 0:
            raise ValueError("the source must have empty history")

    def halted(self, c: Config) -> bool:
        self.validate_config(c)
        return self.instructions[c.state][0] == "halt"

    def selected_branch(self, c: Config) -> Branch | None:
        self.validate_config(c)
        if self.halted(c):
            return None
        for br in self.branches:
            if br.source != c.state:
                continue
            x = c.c0 if br.register == 0 else c.c1
            if br.kind == "inc" or (br.kind == "dec" and x > 0) or (
                br.kind == "zero" and x == 0
            ):
                return br
        raise AssertionError("validated nonhalting state lacks a branch")

    def step(self, c: Config) -> Config | None:
        br = self.selected_branch(c)
        if br is None:
            return None
        values = [c.c0, c.c1]
        values[br.register] += {"inc": 1, "dec": -1, "zero": 0}[br.kind]
        return Config(br.target, *values, self.base * c.history + br.tag)

    def predecessor(self, c: Config) -> Config | None:
        self.validate_config(c)
        h, digit = divmod(c.history, self.base)
        if not 1 <= digit <= len(self.branches):
            return None
        br = self.branches[digit - 1]
        if c.state != br.target:
            return None
        values = [c.c0, c.c1]
        x = values[br.register]
        if br.kind == "inc":
            if x == 0:
                return None
            values[br.register] -= 1
        elif br.kind == "dec":
            values[br.register] += 1
        elif x != 0:
            return None
        prev = Config(br.source, *values, h)
        # This equality also checks the branch guard, not just its affine part.
        return prev if self.step(prev) == c else None

    def neighbors(self, c: Config) -> tuple[Config, ...]:
        p, s = self.predecessor(c), self.step(c)
        return tuple(v for v in (p, s) if v is not None)


def validated_vector(program: Program, vector: Mapping[Config, int]) -> dict[Config, int]:
    if not isinstance(vector, Mapping):
        raise ValueError("vector must be a mapping")
    out = {}
    for v, coefficient in vector.items():
        program.validate_config(v)
        exact_int(coefficient, "coefficient")
        if coefficient:
            out[v] = coefficient
    return out


def apply_l(program: Program, alpha: int, vector: Mapping[Config, int]) -> dict[Config, int]:
    alpha_check(alpha)
    vector = validated_vector(program, vector)
    out = defaultdict(int)
    for v, coefficient in vector.items():
        out[v] += alpha * coefficient
        for w in program.neighbors(v):
            out[w] -= coefficient
    return {v: c for v, c in out.items() if c}


def polynomial_transport(program: Program, vector: Mapping[Config, int],
                         adjoint: bool = False) -> dict[Config, int]:
    """Independent monomial implementation of J_d T and T* C_d.
    It deliberately does not invoke step(), predecessor(), or neighbors().
    """
    vector = validated_vector(program, vector)
    out = defaultdict(int)
    for v, coefficient in vector.items():
        for br in program.branches:
            values = [v.c0, v.c1]
            x = values[br.register]
            if not adjoint:
                if v.state != br.source:
                    continue
                if br.kind == "zero" and x != 0:
                    continue
                if br.kind == "dec" and x == 0:
                    continue
                values[br.register] += {"inc": 1, "dec": -1, "zero": 0}[br.kind]
                w = Config(br.target, *values, program.base * v.history + br.tag)
            else:
                h, digit = divmod(v.history, program.base)
                if v.state != br.target or digit != br.tag:
                    continue
                if br.kind == "zero" and x != 0:
                    continue
                if br.kind == "inc" and x == 0:
                    continue
                values[br.register] += {"inc": -1, "dec": 1, "zero": 0}[br.kind]
                w = Config(br.source, *values, h)
            out[w] += coefficient
    return {v: c for v, c in out.items() if c}


def run(program: Program, source: Config, horizon: int) -> tuple[list[Config], bool]:
    program.validate_config(source, root=True)
    exact_nat(horizon, "horizon")
    trace = [source]
    for _ in range(horizon):
        nxt = program.step(trace[-1])
        if nxt is None:
            return trace, True
        trace.append(nxt)
    return trace, program.halted(trace[-1])


def continuants(alpha: int, n: int) -> list[int]:
    """Return [D_0,...,D_n], with D_-1=0, D_0=1."""
    alpha_check(alpha)
    exact_nat(n, "n")
    ds = [1]
    previous = 0
    for _ in range(n):
        previous, nxt = ds[-1], alpha * ds[-1] - previous
        ds.append(nxt)
    return ds


def certificate(program: Program, source: Config, alpha: int,
                horizon: int) -> tuple[int, dict[Config, int]]:
    alpha_check(alpha)
    trace, halted = run(program, source, horizon)
    if not halted:
        raise TimeoutError("no halt found within the supplied horizon")
    n = len(trace)
    ds = continuants(alpha, n)
    vector = {v: ds[n - i - 1] for i, v in enumerate(trace)}
    return ds[n], vector


def check_certificate(program: Program, source: Config, alpha: int,
                      q: int, vector: Mapping[Config, int],
                      modulus: int | None = None) -> bool:
    program.validate_config(source, root=True)
    exact_int(q, "q")
    alpha_check(alpha)
    vector = validated_vector(program, vector)
    residual = defaultdict(int, apply_l(program, alpha, vector))
    residual[source] -= q
    terminal_sum = sum(c for v, c in vector.items() if program.halted(v))
    if modulus is None:
        return all(r == 0 for r in residual.values()) and terminal_sum == 1
    exact_nat(modulus, "modulus")
    if modulus < 2:
        raise ValueError("modulus must be at least 2")
    return all(r % modulus == 0 for r in residual.values()) and (terminal_sum - 1) % modulus == 0


def rational_level_index(alpha: int, value: Fraction) -> int | None:
    """Return n>=1 when value=D_(n-1)/D_n; otherwise None.
    Descent is exact, terminating, and linear in the number n of descent steps.
    """
    alpha_check(alpha)
    if not isinstance(value, Fraction):
        raise ValueError("value must be fractions.Fraction")
    p, q = value.numerator, value.denominator
    if not 0 < p < q or q*q + p*p - alpha*p*q != 1:
        return None
    n = 0
    while p:
        q, p = p, alpha * p - q
        n += 1
        if p < 0 or p >= q:
            raise AssertionError("Pell descent invariant failed")
    if q != 1:
        raise AssertionError("Pell descent ended at a nonunit")
    return n


def exact_rational_level(program: Program, source: Config, alpha: int,
                         value: Fraction) -> bool:
    program.validate_config(source, root=True)
    n = rational_level_index(alpha, value)
    if n is None:
        return False
    trace, halted = run(program, source, n - 1)
    return halted and len(trace) == n


def green_interval(program: Program, source: Config, alpha: int,
                   bits: int) -> tuple[Fraction, Fraction]:
    """A certified interval of width <= 2**(-bits), including for divergent runs."""
    alpha_check(alpha)
    exact_nat(bits, "bits")
    n = max(1, (bits + 1) // 2)
    trace, halted = run(program, source, n - 1)
    if halted:
        ds = continuants(alpha, len(trace))
        val = Fraction(ds[-2], ds[-1])
        return val, val
    lo, hi = Fraction(0), Fraction(1, 2)
    for _ in range(n):
        lo, hi = 1 / (alpha - lo), 1 / (alpha - hi)
    assert hi - lo <= Fraction(1, 2 ** bits)
    return lo, hi


def slice_rows(program: Program, source: Config, alpha: int,
               support: Sequence[Config]) -> tuple[list[str], list[dict]]:
    """Linear residuals for P_{s,E}; rows include ALL exterior neighbors."""
    program.validate_config(source, root=True)
    alpha_check(alpha)
    if not isinstance(support, (list, tuple)) or len(set(support)) != len(support):
        raise ValueError("support must be a list/tuple of distinct configurations")
    for v in support:
        program.validate_config(v)
    support = tuple(support)
    names = [f"u{i}" for i in range(len(support))] + ["q"]
    index = {v: i for i, v in enumerate(support)}
    closure = {source, *support}
    for v in support:
        closure.update(program.neighbors(v))
    rows = []
    for w in sorted(closure):
        co = defaultdict(int)
        if w in index:
            co[f"u{index[w]}"] += alpha
        for v in program.neighbors(w):
            if v in index:
                co[f"u{index[v]}"] -= 1
        if w == source:
            co["q"] -= 1
        rows.append({"vertex": w.as_list(), "coefficients": dict(co), "constant": 0})
    rows.append({"vertex": "terminal normalization", "coefficients": {
        f"u{i}": 1 for i, v in enumerate(support) if program.halted(v)}, "constant": -1})
    return names, rows


def rows_value(names: list[str], rows: list[dict], values: Mapping[str, int]) -> int:
    if set(values) != set(names):
        raise ValueError("assignment does not match variable names")
    for v in values.values():
        exact_int(v, "assignment value")
    return sum((row["constant"] + sum(c * values[k] for k, c in row["coefficients"].items()))**2
               for row in rows)


def export_example(directory: Path) -> None:
    directory.mkdir(parents=True, exist_ok=True)
    program = Program((("test", 0, 0, 1), ("halt",)))
    source = Config(0, 2, 0)
    q, vector = certificate(program, source, 3, 10)
    trace, _ = run(program, source, 10)
    names, rows = slice_rows(program, source, 3, trace)
    output = {
        "description": "Two-decrement countdown followed by the zero branch; three transitions.",
        "program": program.instructions, "source": source.as_list(), "alpha": 3,
        "base": program.base, "q": q, "green_value": str(Fraction(vector[source], q)),
        "vector": [{"vertex": v.as_list(), "coefficient": vector[v]} for v in trace],
        "variables": names, "residuals": rows,
        "quadratic_semantics": "Sum of squares of every listed residual equals zero.",
        "assignment": {**{f"u{i}": vector[v] for i, v in enumerate(trace)}, "q": q},
    }
    (directory / "countdown.json").write_text(json.dumps(output, indent=2) + "\n")
    p2 = Program((("inc", 0, 0), ("test", 0, 1, 2), ("halt",)))
    nonhalt_source = Config(0, 0, 0)
    dummy = Config(1, 0, 0)
    _, wrong = certificate(p2, dummy, 3, 1)
    wrong = {v: c % 2 for v, c in wrong.items()}
    assert not check_certificate(p2, nonhalt_source, 3, 0, wrong)
    assert check_certificate(p2, nonhalt_source, 3, 0, wrong, modulus=2)
    modular = {"program": p2.instructions, "source": nonhalt_source.as_list(),
               "alpha": 3, "modulus": 2, "q": 0,
               "vector": [{"vertex": v.as_list(), "coefficient": c} for v, c in wrong.items()],
               "note": "Fails over integers; passes modulo 2 for a source that never halts."}
    (directory / "modular_false_positive.json").write_text(json.dumps(modular, indent=2) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--export-example", type=Path)
    args = parser.parse_args()
    if args.export_example is not None:
        export_example(args.export_example)
        print("Exported exact countdown and modular counterexample.")
    else:
        parser.print_help()


if __name__ == "__main__":
    main()

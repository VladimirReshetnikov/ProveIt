#!/usr/bin/env python3
"""Conservative one-fallback register-machine compiler and quartic certificates.

Python 3.10+, standard library only. All polynomial variables range over N.
Run `python code/reaction_compiler.py --output examples` from the package root.
The compiler does not claim to generate a fixed-arity global MRDP polynomial.
"""
from __future__ import annotations
from dataclasses import dataclass
from collections import Counter
from math import comb
from pathlib import Path
import argparse
import json
from typing import Mapping

@dataclass(frozen=True)
class Instruction:
    op: str
    register: int = 0
    positive: str = "H"
    zero: str = "H"

@dataclass(frozen=True)
class Machine:
    registers: int
    instructions: Mapping[str, Instruction]
    start: str
    halt: str = "H"

    def validate(self) -> None:
        if self.registers < 1 or self.start not in self.instructions:
            raise ValueError("Invalid register count or start label")
        if self.halt not in self.instructions or self.instructions[self.halt].op != "halt":
            raise ValueError("A distinguished halt label is required")
        for label, ins in self.instructions.items():
            if ins.op == "halt":
                if label != self.halt:
                    raise ValueError("This normal form uses exactly one halt label")
            elif ins.op in ("inc", "dec"):
                if not 0 <= ins.register < self.registers:
                    raise ValueError("Invalid register index")
                if ins.positive not in self.instructions:
                    raise ValueError("Invalid target label")
                if ins.op == "dec" and ins.zero not in self.instructions:
                    raise ValueError("Invalid zero target")
            else:
                raise ValueError(f"Unknown operation: {ins.op}")

@dataclass(frozen=True)
class Reaction:
    name: str
    reactants: tuple[str, str]
    products: tuple[str, str]
    priority: int

    def enabled(self, x: Mapping[str, int]) -> bool:
        return all(x[s] >= n for s, n in Counter(self.reactants).items())

    def delta(self, species: str) -> int:
        return self.products.count(species) - self.reactants.count(species)

@dataclass(frozen=True)
class Network:
    machine: Machine
    species: tuple[str, ...]
    reactions: tuple[Reaction, ...]

    def initial(self, counters: list[int], fuel: int) -> dict[str, int]:
        if len(counters) != self.machine.registers:
            raise ValueError("Wrong counter-vector length")
        if any(type(v) is not int or v < 0 for v in [*counters, fuel]):
            raise ValueError("Counts must be nonnegative integers")
        x = dict.fromkeys(self.species, 0)
        x.update({f"C{j}": c for j, c in enumerate(counters)})
        x["F"] = fuel
        x["Z"] = 2
        x[f"Q_{self.machine.start}"] = 1
        return x

    def choices(self, x: Mapping[str, int], use_priority: bool = True) -> list[int]:
        indices = [i for i, r in enumerate(self.reactions) if r.enabled(x)]
        if not indices or not use_priority:
            return indices
        maximum = max(self.reactions[i].priority for i in indices)
        return [i for i in indices if self.reactions[i].priority == maximum]

    def fire(self, x: Mapping[str, int], index: int) -> dict[str, int]:
        r = self.reactions[index]
        if not r.enabled(x):
            raise ValueError(f"Reaction {r.name} is not enabled")
        return {s: x[s] + r.delta(s) for s in self.species}

    def step(self, x: Mapping[str, int]) -> tuple[dict[str, int], int | None]:
        choices = self.choices(x)
        if len(choices) > 1:
            raise ValueError("Nondeterministic marking outside the invariant")
        if not choices:
            return dict(x), None  # canonical deadlock/halting padding
        j = choices[0]
        return self.fire(x, j), j

    def phase_count(self) -> int:
        return len(self.machine.instructions) + 3 * sum(
            i.op == "dec" for i in self.machine.instructions.values())

    def horizon(self, storage: int) -> int:
        if storage < 0:
            raise ValueError("Negative storage")
        return self.phase_count() * comb(storage + self.machine.registers,
                                         self.machine.registers)

    def invariant(self, x: Mapping[str, int], storage: int) -> bool:
        if any(type(v) is not int or v < 0 for v in x.values()):
            return False
        if sum(x[f"C{j}"] for j in range(self.machine.registers)) + x["F"] != storage:
            return False
        controls = [s for s in self.species if s.startswith(("Q_", "S_", "R_"))]
        if sum(x[s] for s in controls) != 1:
            return False
        control = next(s for s in controls if x[s] == 1)
        mode = (x["Z"], x["A"], x["B"])
        return ((control.startswith("Q_") and mode == (2, 0, 0)) or
                (control.startswith("S_") and mode in ((1, 1, 0), (1, 0, 1))) or
                (control.startswith("R_") and mode == (1, 1, 0)))


def compile_machine(machine: Machine) -> Network:
    machine.validate()
    q = [f"Q_{label}" for label in machine.instructions]
    dec_labels = [label for label, ins in machine.instructions.items() if ins.op == "dec"]
    species = tuple(q + [f"S_{a}" for a in dec_labels] + [f"R_{a}" for a in dec_labels]
                    + [f"C{j}" for j in range(machine.registers)] + ["F", "Z", "A", "B"])
    rules: list[Reaction] = []
    for label, ins in machine.instructions.items():
        c, source = f"C{ins.register}", f"Q_{label}"
        if ins.op == "inc":
            rules.append(Reaction(f"inc_{label}", (source, "F"),
                                  (f"Q_{ins.positive}", c), 1))
        elif ins.op == "dec":
            rules.extend([
                Reaction(f"enter_{label}", (source, "Z"), (f"S_{label}", "A"), 1),
                Reaction(f"take_{label}", (f"S_{label}", c), (f"R_{label}", "F"), 1),
                Reaction(f"return_{label}", (f"R_{label}", "A"),
                         (f"Q_{ins.positive}", "Z"), 1),
                Reaction(f"zero_{label}", (f"S_{label}", "B"),
                         (f"Q_{ins.zero}", "Z"), 1),
            ])
    rules.append(Reaction("fallback", ("A", "Z"), ("B", "Z"), 0))
    assert all(len(set(r.reactants)) == 2 for r in rules)
    assert len(rules) == len(machine.instructions) + 3 * len(dec_labels)
    return Network(machine, species, tuple(rules))


def universal_machine() -> Machine:
    """23-label, eight-register machine, following the U32 flowchart.

    Relabeling is documented in the article. In particular, l15's zero branch
    goes to l20 (q27 -> q29), as in Figure 1, NOT the conflicting table entry
    q27 -> q1 on page 5 of arXiv:1009.2706. Universality is inherited literature,
    not a claim established by the finite tests in this package.
    Inputs occupy C1 and C2; C0 is the output register.
    """
    I = Instruction
    return Machine(8, {
        "0": I("dec", 1, "1", "2"), "1": I("inc", 7, "0"),
        "2": I("inc", 6, "3"), "3": I("dec", 5, "2", "4"),
        "4": I("dec", 6, "5", "3"), "5": I("inc", 5, "6"),
        "6": I("dec", 7, "7", "8"), "7": I("inc", 1, "4"),
        "8": I("dec", 6, "9", "0"), "9": I("inc", 6, "10"),
        "10": I("dec", 4, "0", "11"), "11": I("dec", 5, "12", "13"),
        "12": I("dec", 5, "14", "15"), "13": I("dec", 2, "18", "19"),
        "14": I("dec", 5, "16", "17"), "15": I("dec", 3, "18", "20"),
        "16": I("inc", 4, "11"), "17": I("inc", 2, "21"),
        "18": I("dec", 4, "0", "H"), "19": I("dec", 0, "0", "18"),
        "20": I("inc", 0, "0"), "21": I("inc", 3, "18"), "H": I("halt"),
    }, "0")


def doubling_machine() -> Machine:
    I = Instruction
    return Machine(2, {"0": I("dec", 0, "1", "H"),
                       "1": I("inc", 1, "2"),
                       "2": I("inc", 1, "0"), "H": I("halt")}, "0")


class Poly:
    """Sparse integer polynomial; monomials are sorted tuples of variable names."""
    def __init__(self, terms: Mapping[tuple[str, ...], int] | int = 0):
        if isinstance(terms, int):
            terms = {(): terms}
        self.terms = {tuple(sorted(m)): int(c) for m, c in terms.items() if c}

    @staticmethod
    def var(name: str) -> Poly:
        return Poly({(name,): 1})

    @staticmethod
    def coerce(x: Poly | int) -> Poly:
        return x if isinstance(x, Poly) else Poly(x)

    def __add__(self, other: Poly | int) -> Poly:
        d = self.terms.copy()
        for m, c in self.coerce(other).terms.items():
            d[m] = d.get(m, 0) + c
        return Poly(d)
    __radd__ = __add__

    def __neg__(self) -> Poly:
        return Poly({m: -c for m, c in self.terms.items()})

    def __sub__(self, other: Poly | int) -> Poly:
        return self + (-self.coerce(other))

    def __rsub__(self, other: Poly | int) -> Poly:
        return self.coerce(other) - self

    def __mul__(self, other: Poly | int) -> Poly:
        d: dict[tuple[str, ...], int] = {}
        for a, ca in self.terms.items():
            for b, cb in self.coerce(other).terms.items():
                m = tuple(sorted(a + b))
                d[m] = d.get(m, 0) + ca * cb
        return Poly(d)
    __rmul__ = __mul__

    def evaluate(self, assignment: Mapping[str, int]) -> int:
        total = 0
        for monomial, coefficient in self.terms.items():
            term = coefficient
            for variable in monomial:
                term *= assignment[variable]
            total += term
        return total

    def degree(self) -> int:
        return max(map(len, self.terms), default=0)

    def records(self) -> list[dict]:
        return [{"coefficient": c, "variables": list(m)}
                for m, c in sorted(self.terms.items(), key=lambda item: (len(item[0]), item[0]))]


@dataclass
class Certificate:
    witnesses: list[str]
    residuals: list[tuple[str, Poly]]

    def violations(self, assignment: Mapping[str, int]) -> dict[str, int]:
        if any(type(v) is not int or v < 0 for v in assignment.values()):
            raise ValueError("Certificate assignments must be natural numbers")
        return {name: v for name, poly in self.residuals
                if (v := poly.evaluate(assignment)) != 0}

    def value(self, assignment: Mapping[str, int]) -> int:
        return sum(v * v for v in self.violations(assignment).values())

    def expanded(self) -> Poly:
        result = Poly()
        for _, p in self.residuals:
            result = result + p * p
        return result


def zero_residuals(x: Poly, z: Poly, b: Poly) -> list[Poly]:
    return [z * (z - 1), x * z, x - (1 - z) * (b + 1), z * b]


def trace_certificate(net: Network, initial: Mapping[str, Poly | int], horizon: int,
                      endpoint: Poly | int = 1, prefix: str = "t") -> Certificate:
    if horizon < 0:
        raise ValueError("Negative horizon")
    names: list[str] = []
    def v(kind: str, t: int, i: str | int) -> Poly:
        name = f"{prefix}_{kind}_{t}_{i}"
        names.append(name)
        return Poly.var(name)
    d, r = len(net.species), len(net.reactions)
    xs = [{s: v("x", t, s) for s in net.species} for t in range(horizon + 1)]
    zs = [{s: v("z", t, s) for s in net.species} for t in range(horizon)]
    bs = [{s: v("b", t, s) for s in net.species} for t in range(horizon)]
    es = [[v("e", t, j) for j in range(r)] for t in range(horizon)]
    ss = [[v("s", t, j) for j in range(r + 1)] for t in range(horizon)]
    residuals: list[tuple[str, Poly]] = []
    def add(label: str, p: Poly) -> None:
        if p.degree() > 2:
            raise AssertionError("A residual exceeded degree two")
        residuals.append((f"{prefix}:{label}", p))
    for s in net.species:
        add(f"initial:{s}", xs[0][s] - initial[s])
    low = next(j for j, rr in enumerate(net.reactions) if rr.priority == 0)
    for t in range(horizon):
        for species in net.species:
            for a, polynomial in enumerate(zero_residuals(xs[t][species], zs[t][species], bs[t][species])):
                add(f"zero:{t}:{species}:{a}", polynomial)
        for j, rr in enumerate(net.reactions):
            u, w = rr.reactants
            add(f"enabled:{t}:{j}", es[t][j] - (1 - zs[t][u]) * (1 - zs[t][w]))
        for j in range(r + 1):
            add(f"selector:{t}:{j}", ss[t][j] * (ss[t][j] - 1))
        add(f"one:{t}", sum(ss[t], Poly()) - 1)
        for j in range(r):
            add(f"eligible:{t}:{j}", ss[t][j] * (1 - es[t][j]))
            add(f"idle:{t}:{j}", ss[t][r] * es[t][j])
            if j != low:
                add(f"priority:{t}:{j}", ss[t][low] * es[t][j])
        for species in net.species:
            delta = sum((ss[t][j] * rr.delta(species)
                         for j, rr in enumerate(net.reactions)), Poly())
            add(f"update:{t}:{species}", xs[t + 1][species] - xs[t][species] - delta)
    add("endpoint", xs[horizon][f"Q_{net.machine.halt}"] - endpoint)
    assert len(names) == (3 * d + 2 * r + 1) * horizon + d
    assert len(residuals) == (5 * d + 5 * r + 1) * horizon + d + 1
    return Certificate(names, residuals)


def trace_assignment(net: Network, initial: Mapping[str, int], horizon: int,
                     prefix: str = "t", forced: list[int | None] | None = None) -> dict[str, int]:
    assignment: dict[str, int] = {}
    x = dict(initial)
    r = len(net.reactions)
    for t in range(horizon + 1):
        for s in net.species:
            assignment[f"{prefix}_x_{t}_{s}"] = x[s]
        if t == horizon:
            break
        for s in net.species:
            assignment[f"{prefix}_z_{t}_{s}"] = int(x[s] == 0)
            assignment[f"{prefix}_b_{t}_{s}"] = max(0, x[s] - 1)
        for j, rr in enumerate(net.reactions):
            assignment[f"{prefix}_e_{t}_{j}"] = int(rr.enabled(x))
        if forced is None:
            y, chosen = net.step(x)
        else:
            chosen = forced[t]
            y = dict(x) if chosen is None else net.fire(x, chosen)
        for j in range(r + 1):
            assignment[f"{prefix}_s_{t}_{j}"] = int(j == (r if chosen is None else chosen))
        x = y
    return assignment


def initial_polynomials(net: Network, counters: list[Poly | int], fuel: Poly | int) -> dict[str, Poly | int]:
    x: dict[str, Poly | int] = dict.fromkeys(net.species, 0)
    x.update({f"C{j}": a for j, a in enumerate(counters)})
    x["F"], x["Z"], x[f"Q_{net.machine.start}"] = fuel, 2, 1
    return x


def minimum_certificate(net: Network, counters: list[Poly | int], fuel: Poly,
                        storage_expression: Poly, limit: int) -> Certificate:
    T = net.horizon(limit)
    z, b, slack = (Poly.var(v) for v in ("df", "bf", "slack"))
    first = trace_certificate(net, initial_polynomials(net, counters, fuel), T, 1, "u")
    second = trace_certificate(net, initial_polynomials(net, counters, b), T, z, "v")
    res = first.residuals + second.residuals
    res += [(f"fuelzero:{j}", p) for j, p in enumerate(zero_residuals(fuel, z, b))]
    res += [("massbound", storage_expression + slack - limit)]
    return Certificate(first.witnesses + second.witnesses + ["df", "bf", "slack"], res)


def network_json(net: Network) -> dict:
    return {"species": list(net.species), "reactions": [
        {"name": r.name, "reactants": list(r.reactants), "products": list(r.products),
         "priority": r.priority} for r in net.reactions],
        "start_label": net.machine.start, "halt_label": net.machine.halt,
        "registers": net.machine.registers, "initial_mode": {"Z": 2, "A": 0, "B": 0},
        "semantics": "An enabled high-priority reaction suppresses the unique low-priority reaction."}


def write_examples(output: Path) -> dict:
    output.mkdir(parents=True, exist_ok=True)
    universal = compile_machine(universal_machine())
    (output / "universal_61_species_62_reactions.json").write_text(
        json.dumps(network_json(universal), indent=2) + "\n")
    lines = ["# High priority = 1; low priority = 0. Initial mode: two Z molecules."]
    for r in universal.reactions:
        lines.append(f"[{r.priority}] {r.name}: {' + '.join(r.reactants)} -> {' + '.join(r.products)}")
    (output / "universal_reactions.txt").write_text("\n".join(lines) + "\n")
    toy = compile_machine(doubling_machine())
    n, fuel = Poly.var("n"), Poly.var("f")
    cert = trace_certificate(toy, initial_polynomials(toy, [n, 0], fuel), 8)
    witness = trace_assignment(toy, toy.initial([1, 0], 1), 8)
    assignment = {"n": 1, "f": 1, **witness}
    assert cert.value(assignment) == 0
    polynomial = cert.expanded()
    assert polynomial.degree() == 4 and polynomial.evaluate(assignment) == 0
    (output / "doubling_T8_witness.json").write_text(json.dumps(assignment, indent=2) + "\n")
    (output / "doubling_T8_quartic.json").write_text(json.dumps({
        "parameters": ["n", "f"], "witnesses": cert.witnesses,
        "semantics": "sum of squared quadratic residuals; all variables are natural numbers",
        "terms": polynomial.records()}, separators=(",", ":")) + "\n")
    (output / "doubling_T8_residuals.json").write_text(json.dumps({
        "residuals": [{"name": label, "terms": p.records()} for label, p in cert.residuals]},
        separators=(",", ":")) + "\n")
    result = {"universal_species": len(universal.species),
              "universal_reactions": len(universal.reactions),
              "toy_horizon": 8, "toy_witness_variables": len(cert.witnesses),
              "toy_quadratic_residuals": len(cert.residuals),
              "toy_expanded_quartic_monomials": len(polynomial.terms),
              "toy_polynomial_degree": polynomial.degree(), "toy_witness_value": 0}
    (output / "example_summary.json").write_text(json.dumps(result, indent=2) + "\n")
    return result

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("examples"))
    args = parser.parse_args()
    print(json.dumps(write_examples(args.output), indent=2))

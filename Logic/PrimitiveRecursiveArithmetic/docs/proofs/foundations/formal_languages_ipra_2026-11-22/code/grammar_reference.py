#!/usr/bin/env python3
"""Independent executable checks for the CFG constructions.

The direct fixed-point parser accepts arbitrary finite CFGs, including epsilon
and unit cycles. It is compared with an epsilon/unit elimination + CNF + CYK
pipeline. These finite checks are not Lean verification or a proof in iPRA.
Python 3.10+, standard library only.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from pathlib import Path
import json
import random

Symbol = tuple[str, str]


def N(name: str) -> Symbol:
    return ("N", name)


def T(letter: str) -> Symbol:
    return ("T", letter)


@dataclass(frozen=True)
class Rule:
    lhs: str
    rhs: tuple[Symbol, ...]


@dataclass(frozen=True)
class Grammar:
    start: str
    nonterminals: tuple[str, ...]
    alphabet: tuple[str, ...]
    rules: tuple[Rule, ...]

    def validate(self) -> None:
        assert self.start in self.nonterminals
        for rule in self.rules:
            assert rule.lhs in self.nonterminals
            for kind, item in rule.rhs:
                assert (kind == "N" and item in self.nonterminals) or (
                    kind == "T" and item in self.alphabet
                )


@dataclass(frozen=True)
class Tree:
    root: str
    children: tuple["Tree | str", ...]


def check_tree(g: Grammar, t: Tree) -> tuple[str, ...]:
    rhs: list[Symbol] = []
    result: list[str] = []
    for child in t.children:
        if isinstance(child, Tree):
            rhs.append(N(child.root))
            result.extend(check_tree(g, child))
        else:
            rhs.append(T(child))
            result.append(child)
    assert Rule(t.root, tuple(rhs)) in g.rules
    return tuple(result)


def direct_parse(g: Grammar, w: tuple[str, ...]) -> Tree | None:
    """Synchronous saturation, independent of normalization and CYK."""
    n = len(w)
    chart: dict[tuple[str, int, int], Tree] = {}
    capacity = len(g.nonterminals) * (n + 1) * (n + 2) // 2
    for _round in range(capacity + 1):
        old = dict(chart)
        for rule in g.rules:
            for i in range(n + 1):
                possible: dict[int, tuple[Tree | str, ...]] = {i: ()}
                for kind, item in rule.rhs:
                    following: dict[int, tuple[Tree | str, ...]] = {}
                    for pos, children in possible.items():
                        if kind == "T":
                            if pos < n and w[pos] == item:
                                following.setdefault(pos + 1, children + (item,))
                        else:
                            for end in range(pos, n + 1):
                                child = old.get((item, pos, end))
                                if child is not None:
                                    following.setdefault(end, children + (child,))
                    possible = following
                for j, children in possible.items():
                    chart.setdefault((rule.lhs, i, j), Tree(rule.lhs, children))
        if chart.keys() == old.keys():
            return chart.get((g.start, 0, n))
    raise AssertionError("The finite chart failed to stabilize within its bound")


def cnf(g: Grammar) -> Grammar:
    """Fresh start; nullable deletion; unit closure; terminals; binarization."""
    g.validate()
    names = list(g.nonterminals)

    def fresh(prefix: str) -> str:
        index = 0
        while f"{prefix}{index}" in names:
            index += 1
        name = f"{prefix}{index}"
        names.append(name)
        return name

    start = fresh("Start")
    rules = set(g.rules) | {Rule(start, (N(g.start),))}
    nullable: set[str] = set()
    for _ in range(len(names)):
        old = set(nullable)
        nullable |= {
            r.lhs for r in rules
            if all(kind == "N" and item in old for kind, item in r.rhs)
        }
    deleted: set[Rule] = set()
    for r in rules:
        choices = [
            ((s,), ()) if s[0] == "N" and s[1] in nullable else ((s,),)
            for s in r.rhs
        ]
        for selection in product(*choices):
            rhs = tuple(s for block in selection for s in block)
            if rhs or r.lhs == start:
                deleted.add(Rule(r.lhs, rhs))
    units = {(r.lhs, r.rhs[0][1]) for r in deleted
             if len(r.rhs) == 1 and r.rhs[0][0] == "N"}
    reachable = {a: {a} for a in names}
    for _ in range(len(names)):
        old = {a: set(bs) for a, bs in reachable.items()}
        for a in names:
            for b, c in units:
                if b in old[a]:
                    reachable[a].add(c)
    nonunit = {r for r in deleted
               if not (len(r.rhs) == 1 and r.rhs[0][0] == "N")}
    rules = {Rule(a, r.rhs) for a in names for r in nonunit
             if r.lhs in reachable[a]}
    terminal_names: dict[str, str] = {}
    isolated: set[Rule] = set()
    for r in sorted(rules, key=repr):
        if len(r.rhs) < 2:
            isolated.add(r)
            continue
        rhs = []
        for symbol in r.rhs:
            if symbol[0] == "T":
                a = symbol[1]
                if a not in terminal_names:
                    terminal_names[a] = fresh("Terminal")
                rhs.append(N(terminal_names[a]))
            else:
                rhs.append(symbol)
        isolated.add(Rule(r.lhs, tuple(rhs)))
    for a, name in terminal_names.items():
        isolated.add(Rule(name, (T(a),)))
    binary: set[Rule] = set()
    for r in sorted(isolated, key=repr):
        if len(r.rhs) <= 2:
            binary.add(r)
            continue
        current = r.lhs
        for i in range(len(r.rhs) - 2):
            following = fresh("Tail")
            binary.add(Rule(current, (r.rhs[i], N(following))))
            current = following
        binary.add(Rule(current, r.rhs[-2:]))
    result = Grammar(start, tuple(names), g.alphabet, tuple(sorted(binary, key=repr)))
    result.validate()
    for r in result.rules:
        assert r.rhs != (N(start),)
        assert all(s != N(start) for s in r.rhs)
        assert (not r.rhs and r.lhs == start) or (
            len(r.rhs) == 1 and r.rhs[0][0] == "T"
        ) or (len(r.rhs) == 2 and all(s[0] == "N" for s in r.rhs))
    return result


def cyk(g: Grammar, w: tuple[str, ...]) -> Tree | None:
    n = len(w)
    if n == 0:
        return Tree(g.start, ()) if Rule(g.start, ()) in g.rules else None
    chart: dict[tuple[str, int, int], Tree] = {}
    for i, a in enumerate(w):
        for r in g.rules:
            if r.rhs == (T(a),):
                chart[(r.lhs, i, i + 1)] = Tree(r.lhs, (a,))
    binary = [r for r in g.rules if len(r.rhs) == 2]
    for length in range(2, n + 1):
        for i in range(n - length + 1):
            j = i + length
            for r in binary:
                b, c = r.rhs[0][1], r.rhs[1][1]
                for k in range(i + 1, j):
                    left, right = chart.get((b, i, k)), chart.get((c, k, j))
                    if left is not None and right is not None:
                        chart.setdefault((r.lhs, i, j), Tree(r.lhs, (left, right)))
    return chart.get((g.start, 0, n))


def words(alphabet: tuple[str, ...], maximum: int):
    for n in range(maximum + 1):
        yield from product(alphabet, repeat=n)


def examples() -> list[Grammar]:
    return [
        Grammar("S", ("S",), ("a", "b"), (
            Rule("S", ()), Rule("S", (T("a"), N("S"), T("b"))))),
        Grammar("S", ("S",), ("(", ")"), (
            Rule("S", ()), Rule("S", (T("("), N("S"), T(")"), N("S"))))),
        Grammar("S", ("S", "A", "B"), ("a", "b"), (
            Rule("S", (N("A"), N("B"))), Rule("A", (N("B"),)),
            Rule("B", (N("A"),)), Rule("A", ()),
            Rule("B", (T("b"),)), Rule("A", (T("a"), N("A"))))),
        Grammar("S", ("S", "A"), ("a", "b"), (
            Rule("S", (N("A"),)), Rule("A", (N("S"),)))),
        Grammar("S", ("S", "A"), ("a", "b"), (
            Rule("S", (N("S"), N("S"))), Rule("S", ()),
            Rule("S", (T("a"),)), Rule("A", (T("b"),)))),
    ]


def run_checks() -> dict:
    grammars = examples()
    for seed in range(32):
        rng = random.Random(seed)
        nts = ("S", "A")
        alphabet = ("a", "b")
        symbols = (N("S"), N("A"), T("a"), T("b"))
        rules = tuple(Rule(rng.choice(nts), tuple(rng.choice(symbols)
                        for _ in range(rng.randrange(4)))) for _ in range(7))
        grammars.append(Grammar("S", nts, alphabet, rules))
    comparisons = certificates = 0
    for g in grammars:
        normalized = cnf(g)
        for w in words(g.alphabet, 5):
            direct = direct_parse(g, w)
            binary = cyk(normalized, w)
            assert (direct is None) == (binary is None), (g, w)
            comparisons += 1
            for grammar, tree in ((g, direct), (normalized, binary)):
                if tree is not None:
                    assert tree.root == grammar.start
                    assert check_tree(grammar, tree) == w
                    certificates += 1
    return {
        "status": "passed", "grammar_count": len(grammars),
        "word_comparisons": comparisons, "parse_certificates_checked": certificates,
        "max_word_length": 5, "random_grammar_seeds": list(range(32)),
        "method": "Independent arbitrary-CFG saturation versus CNF normalization plus CYK",
        "foundational_status": "finite executable checks; not a formal proof",
    }


if __name__ == "__main__":
    report = run_checks()
    destination = Path(__file__).resolve().parents[1] / "qa" / "grammar_checks.json"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))

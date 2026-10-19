#!/usr/bin/env python3
"""Check additive-output commutations against the frozen closed register AST.

This is a finite syntactic certificate checker and reusable trace normalizer.
It proves no transition-table simulation by itself.  See trace_commutation.tex
for the ordinary partial-map argument justifying the independence relation.
All input artifacts are read only.  Python 3.10+, standard library only.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from dataclasses import dataclass
from functools import cache
import hashlib
import heapq
import json
from pathlib import Path


@dataclass(frozen=True)
class Effect:
    touched: frozenset[int]
    tested: frozenset[int]
    has_halt: bool
    bounds: tuple[int, int]


class TraceNormalizer:
    def __init__(self, source: dict, symbols: dict[str, str], strict=False):
        self.source = source
        self.symbols = dict(symbols)
        self.strict = strict
        ast = source["ast_dag"]

        @cache
        def effect(i):
            row = ast[i]
            if row[0] == "L":
                op, *args = row[1]
                if op not in {"inc", "dec", "brk", "cont", "halt"}:
                    raise ValueError(f"unknown register instruction {row[1]}")
                if op in {"inc", "dec"}:
                    if len(args) != 1 or type(args[0]) is not int or not 0 <= args[0] < 9:
                        raise ValueError("invalid register argument")
                    touched = frozenset(args)
                else:
                    touched = frozenset()
                tested = touched if op == "dec" else frozenset()
                bounds = ((1, 0) if op == "dec" else
                          (args[0], 0) if op == "brk" else
                          (0, args[0]) if op == "cont" else (0, 0))
                return Effect(touched, tested, op == "halt", bounds)
            if row[0] != "N" or len(row) != 3:
                raise ValueError(f"bad AST row {row}")
            a, b = effect(row[1]), effect(row[2])
            bounds = (max(a.bounds[0] - 1, b.bounds[0], 0),
                      max(a.bounds[1], b.bounds[1] - 1, 0))
            return Effect(a.touched | b.touched, a.tested | b.tested,
                          a.has_halt or b.has_halt, bounds)

        self.effects = {}
        self.atom_ast = {}
        for c, name in sorted(symbols.items()):
            i = source["atoms"][name]["ast"]
            self.atom_ast[c] = i
            self.effects[c] = effect(i)
            if self.effects[c].bounds != (0, 0):
                raise ValueError(f"atom {c} is not a closed fragment")
        self.alphabet = tuple(sorted(symbols))
        self.independence = {
            (a, b): self._criterion(a, b)
            for a in self.alphabet for b in self.alphabet
        }
        self.dependent = {
            a: tuple(b for b in self.alphabet if not self.independence[a, b])
            for a in self.alphabet
        }

    def _criterion(self, a, b):
        # Trace-theoretic independence is conventionally irreflexive; swapping
        # two identical atoms has no effect on the displayed word anyway.
        if a == b:
            return False
        x, y = self.effects[a], self.effects[b]
        if x.has_halt or y.has_halt:
            return False
        if self.strict:
            return not (x.touched & y.touched)
        return not (x.tested & y.touched or y.tested & x.touched)

    def independent(self, a, b):
        return self.independence[a, b]

    def occurrence_order(self, word):
        """Lexicographically least topological order of the dependence DAG.

        Edges from the last preceding occurrence of every dependent label
        generate all necessary precedence constraints: earlier occurrences of
        a fixed label precede its last occurrence by the same-label chain.
        """
        n = len(word)
        indegree = [0] * n
        outgoing = [[] for _ in range(n)]
        last = {}
        for i, c in enumerate(word):
            if c not in self.effects:
                raise ValueError(f"unknown semantic atom {c!r}")
            parents = [last[d] for d in self.dependent[c] if d in last]
            indegree[i] = len(parents)
            for j in parents:
                outgoing[j].append(i)
            last[c] = i
        ready = [(word[i], i) for i, d in enumerate(indegree) if d == 0]
        heapq.heapify(ready)
        order = []
        while ready:
            _, i = heapq.heappop(ready)
            order.append(i)
            for j in outgoing[i]:
                indegree[j] -= 1
                if indegree[j] == 0:
                    heapq.heappush(ready, (word[j], j))
        if len(order) != n:
            raise AssertionError("dependence DAG contains a cycle")
        return order

    @cache
    def normalize(self, word):
        return "".join(word[i] for i in self.occurrence_order(word))

    def certificate(self, word):
        order = self.occurrence_order(word)
        current = list(range(len(word)))
        swaps = []
        for target, occurrence in enumerate(order):
            j = current.index(occurrence, target)
            while j > target:
                a, b = word[current[j - 1]], word[current[j]]
                if not self.independent(a, b):
                    raise AssertionError(f"noncommuting crossing: {a}, {b}")
                current[j - 1], current[j] = current[j], current[j - 1]
                swaps.append(j - 1)
                j -= 1
        cert = {"before": word, "after": "".join(word[i] for i in order),
                "adjacent_swaps": swaps}
        self.check_certificate(cert)
        return cert

    def check_certificate(self, cert):
        current = list(cert["before"])
        for i in cert["adjacent_swaps"]:
            if type(i) is not int or not 0 <= i < len(current) - 1:
                raise ValueError("invalid adjacent-swap index")
            if not self.independent(current[i], current[i + 1]):
                raise ValueError("certificate swaps dependent atoms")
            current[i], current[i + 1] = current[i + 1], current[i]
        if "".join(current) != cert["after"]:
            raise ValueError("swap certificate has incorrect endpoint")
        return True


def analyze(source_path, symbols_path, grammar_path):
    source = json.loads(source_path.read_text())
    symbols = json.loads(symbols_path.read_text())
    lines = grammar_path.read_text().splitlines()
    nr, nroots, na = map(int, lines[0].split())
    grammar = [(int(k), word, int(q)) for k, word, q in
               (line.split() for line in lines[1:1 + nr])]
    roots = lines[1 + nr:1 + nr + nroots]
    if na != len(symbols):
        raise ValueError("grammar and symbol vocabulary disagree")
    results = {}
    for strict in [True, False]:
        tr = TraceNormalizer(source, symbols, strict=strict)
        groups = defaultdict(list)
        for _, word, state in grammar:
            groups[tr.normalize(word)].append({"state": state, "word": word})
        certificates = [tr.certificate(word) for word in roots]
        # Local tests of the congruence law, idempotence and swapped-pair law.
        for _, word, _ in grammar:
            nf = tr.normalize(word)
            if tr.normalize(nf) != nf:
                raise AssertionError("normal form is not idempotent")
            for k in range(len(word) + 1):
                if tr.normalize(tr.normalize(word[:k]) + tr.normalize(word[k:])) != nf:
                    raise AssertionError("normal form fails concatenation congruence")
        for a in tr.alphabet:
            for b in tr.alphabet:
                if tr.independent(a, b) and tr.normalize(a + b) != tr.normalize(b + a):
                    raise AssertionError("normal form fails independent swap")
        results["strict_disjoint" if strict else "additive_outputs"] = {
            "ordered_independent_pairs": sum(tr.independence.values()),
            "unordered_independent_pairs": sum(tr.independence.values()) // 2,
            "root_adjacent_opportunities": sum(tr.independent(a, b)
                for word in roots for a, b in zip(word, word[1:])),
            "changed_root_normal_forms": sum(c["before"] != c["after"] for c in certificates),
            "root_normalization_swaps": sum(len(c["adjacent_swaps"]) for c in certificates),
            "duplicate_existing_grammar_classes": [g for g in groups.values() if len(g) > 1],
            "root_certificates": certificates,
        }
    tr = TraceNormalizer(source, symbols)
    return {
        "status": "PASS",
        "scope": "Finite AST footprint and trace-equivalence certificates, not a new TM bound",
        "inputs": {str(p): hashlib.sha256(p.read_bytes()).hexdigest()
                   for p in [source_path, symbols_path, grammar_path]},
        "grammar_rules": nr, "roots": nroots, "atoms": na,
        "excluded_halt_atoms": [c for c, e in tr.effects.items() if e.has_halt],
        "atom_effects": {
            c: {"ast": tr.atom_ast[c], "touched": sorted(e.touched),
                "tested": sorted(e.tested), "halt": e.has_halt,
                "closed_bounds": list(e.bounds)} for c, e in tr.effects.items()
        },
        "independent_pairs": [a + b for a in tr.alphabet for b in tr.alphabet
                              if a < b and tr.independent(a, b)],
        "analyses": results,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inputs", type=Path, required=True)
    parser.add_argument("--grammar", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = analyze(args.inputs / "closed-sequence-grammar-next22.json",
                     args.inputs / "semantic-symbols.json", args.grammar)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    summary = {k: v for k, v in result.items() if k not in
               {"atom_effects", "independent_pairs", "analyses"}}
    summary["analyses"] = {k: {a: b for a, b in v.items() if a != "root_certificates"}
                           for k, v in result["analyses"].items()}
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()

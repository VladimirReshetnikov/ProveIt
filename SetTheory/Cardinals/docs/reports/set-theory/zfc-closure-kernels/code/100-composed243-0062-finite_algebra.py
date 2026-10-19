#!/usr/bin/env python3
"""Exact finite-algebra certificates for finite GROUND clause sets.

This is an executable reference specification, not a TM compiler. A finite
stage is checked only at its explicitly listed ground clauses. It is never
interpreted as a universally quantified theory over the entire finite carrier.
No resource limit or execution failure is converted into UNSAT.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
from pathlib import Path
from typing import Iterable


@dataclass(frozen=True)
class Term:
    name: str
    args: tuple[Term, ...] = ()


@dataclass(frozen=True)
class Literal:
    positive: bool
    predicate: str
    args: tuple[Term, ...]


def term(name: str, *args: Term) -> Term:
    return Term(name, tuple(args))


def atom(predicate: str, *args: Term, positive: bool = True) -> Literal:
    return Literal(positive, predicate, tuple(args))


def eq(left: Term, right: Term, positive: bool = True) -> Literal:
    return atom("=", left, right, positive=positive)


def tuple_index(values: Iterable[int], base: int) -> int:
    result = 0
    for value in values:
        result = result * base + value
    return result


class GroundStage:
    """Infer a finite signature and m=max(1,number of ground subterms)."""

    def __init__(self, clauses: Iterable[Iterable[Literal]]):
        self.clauses = tuple(tuple(clause) for clause in clauses)
        arities: dict[str, int] = {}
        predicates: dict[str, int] = {}
        heights: dict[Term, int] = {}

        def declare(table, name, arity):
            if type(name) is not str or not name:
                raise ValueError("Symbol names must be nonempty strings")
            if name in table and table[name] != arity:
                raise ValueError("Inconsistent symbol arity: " + name)
            table[name] = arity

        def collect(t):
            if not isinstance(t, Term) or type(t.args) is not tuple:
                raise ValueError("A ground term must be a finite Term tree")
            if t in heights:
                return heights[t]
            declare(arities, t.name, len(t.args))
            height = 1 + max((collect(a) for a in t.args), default=-1)
            heights[t] = height
            return height

        for clause in self.clauses:
            for literal in clause:
                if not isinstance(literal, Literal):
                    raise ValueError("Expected a signed ground literal")
                if type(literal.positive) is not bool or type(literal.args) is not tuple:
                    raise ValueError("Malformed literal sign or arguments")
                if literal.predicate == "=":
                    if len(literal.args) != 2:
                        raise ValueError("Logical equality is binary")
                else:
                    declare(predicates, literal.predicate, len(literal.args))
                for argument in literal.args:
                    collect(argument)
        # A nonempty carrier is needed even for an empty signature.
        if not heights:
            collect(term("__dummy"))
        self.subterms = tuple(sorted(heights, key=lambda t: (heights[t], repr(t))))
        self.m = len(self.subterms)
        self.functions = tuple(sorted(arities.items()))
        self.predicates = tuple(sorted(predicates.items()))
        self.function_offsets, self.function_cells = self._offsets(self.functions)
        self.predicate_offsets, self.predicate_cells = self._offsets(self.predicates)
        self.function_limit = self.m ** self.function_cells
        self.candidate_count = self.function_limit * (1 << self.predicate_cells)

    def _offsets(self, signature):
        offsets, total = {}, 0
        for name, arity in signature:
            offsets[name] = total
            total += self.m ** arity
        return offsets, total

    def _check_candidate(self, candidate):
        if type(candidate) is not int or not 0 <= candidate < self.candidate_count:
            raise ValueError("Candidate outside the exact finite range")

    def term_values(self, candidate: int) -> dict[Term, int]:
        self._check_candidate(candidate)
        operations = candidate % self.function_limit
        values: dict[Term, int] = {}
        for t in self.subterms:
            position = self.function_offsets[t.name] + tuple_index(
                (values[a] for a in t.args), self.m)
            values[t] = (operations // (self.m ** position)) % self.m
        return values

    def valid(self, candidate: int) -> bool:
        """Only native clauses; no equality-axiom or congruence checks."""
        values = self.term_values(candidate)
        relations = candidate // self.function_limit

        def true(literal):
            args = tuple(values[t] for t in literal.args)
            if literal.predicate == "=":
                value = args[0] == args[1]
            else:
                position = self.predicate_offsets[literal.predicate] + tuple_index(
                    args, self.m)
                value = bool((relations >> position) & 1)
            return value == literal.positive

        return all(any(true(literal) for literal in clause) for clause in self.clauses)

    def decide(self) -> dict:
        """UNSAT is returned only after exact finite exhaustion."""
        for candidate in range(self.candidate_count):
            if self.valid(candidate):
                return {"status": "SAT", "witness": candidate,
                        "candidates_checked": candidate + 1}
        return {"status": "UNSAT", "witness": None,
                "candidates_checked": self.candidate_count}

    def encode(self, operation_tables: dict, relation_tables: dict) -> int:
        """Encode explicit total tables; a witness-construction helper."""
        operations = 0
        for name, arity in self.functions:
            table = tuple(operation_tables[name])
            if len(table) != self.m ** arity:
                raise ValueError("Incorrect operation-table length")
            for i, value in enumerate(table):
                if type(value) is not int or not 0 <= value < self.m:
                    raise ValueError("Operation-table value outside carrier")
                operations += value * self.m ** (self.function_offsets[name] + i)
        relations = 0
        for name, arity in self.predicates:
            table = tuple(relation_tables[name])
            if len(table) != self.m ** arity or any(type(b) is not bool for b in table):
                raise ValueError("Malformed relation table")
            for i, value in enumerate(table):
                relations |= int(value) << (self.predicate_offsets[name] + i)
        return operations + self.function_limit * relations

    def cost(self) -> dict:
        return {"carrier_size": self.m, "distinct_subterms": len(self.subterms),
                "function_cells": self.function_cells,
                "predicate_bits": self.predicate_cells,
                "candidate_count": self.candidate_count,
                "minimum_fixed_binary_bits": (self.candidate_count - 1).bit_length()}


def finite_checks() -> dict:
    c, d = term("c"), term("d")
    f = lambda x: term("f", x)
    cases = [
        ("empty_clause", [()], "UNSAT"),
        ("complementary_membership", [(atom("R", c, c),),
                                     (atom("R", c, c, positive=False),)], "UNSAT"),
        ("function_congruence", [(eq(c, d),),
                                 (eq(f(c), f(d), False),)], "UNSAT"),
        ("membership_transport", [(eq(c, d),), (atom("R", c, c),),
                                  (atom("R", d, d, positive=False),)], "UNSAT"),
        ("functions_need_not_be_injective", [(eq(f(c), f(d)),),
                                              (eq(c, d, False),)], "SAT"),
        ("composite_congruence", [(eq(f(c), c),),
                                  (eq(f(f(c)), f(c), False),)], "UNSAT"),
        # A disjunctive clause is evaluated together with a disequality unit.
        ("disjunctive_equality", [(eq(c, d), eq(f(c), f(d), False)),
                                   (eq(c, d, False),)], "SAT"),
    ]
    outcomes = []
    for name, clauses, expected in cases:
        stage = GroundStage(clauses)
        outcome = stage.decide()
        if outcome["status"] != expected:
            raise AssertionError((name, outcome, expected))
        outcomes.append({"name": name, **stage.cost(), **outcome})

    # The infinite universal theory has injective s with c outside its image.
    # It has no finite model. Every listed finite ground stage has a finite
    # algebra certificate: use an (n+1)-cycle, whose last wrapping edge is not
    # demanded by any ground clause at this stage.
    prefixes = []
    for n in range(1, 7):
        chain = [c]
        for _ in range(n):
            chain.append(term("s", chain[-1]))
        clauses = [(eq(c, chain[i + 1], False),) for i in range(n)]
        clauses += [(eq(chain[i + 1], chain[j + 1], False), eq(chain[i], chain[j]))
                    for i in range(n) for j in range(n)]
        stage = GroundStage(clauses)
        operations = {"c": [0], "s": list(range(1, n + 1)) + [0]}
        witness = stage.encode(operations, {})
        if stage.m != n + 1 or not stage.valid(witness):
            raise AssertionError("Finite-ground/full-universal distinction failed")
        prefixes.append({"depth": n, "clauses": len(clauses), **stage.cost(),
                         "witness": witness, "witness_valid": True,
                         "full_theory_holds_in_witness": False})
    return {"method": "exact total finite algebras for finite ground clauses",
            "cases": outcomes, "infinite_only_theory_ground_prefixes": prefixes,
            "state_count_claim": None, "full_zfc_generator_implemented": False,
            "all_checks_passed": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = finite_checks()
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()

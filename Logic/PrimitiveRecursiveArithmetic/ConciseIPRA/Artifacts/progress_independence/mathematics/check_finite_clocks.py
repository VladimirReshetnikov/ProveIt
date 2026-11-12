#!/usr/bin/env python3
"""Evaluate the scalar clock terms on bounded standard inputs.

This is executable corroboration of finite examples, NOT a proof checker for
the theorem and NOT a formal verification of any universal assertion. The
LaTeX proof establishes the unbounded result. Every generated expression uses
only variables, zero, successor, and the scalar iterator, with de Bruijn
indices; repeated subexpressions are stored as a DAG, without new primitives.

Run: python3 check_finite_clocks.py --max-period 12 --max-input 32
"""

import argparse
import functools
import json


class ScalarTerms:
    def __init__(self):
        self.nodes = []
        self.interned = {}
        self.zero = self.node("z")
        self.var = self.node("v", 0)
        self.one = self.succ(self.zero)

    def node(self, *description):
        if description not in self.interned:
            self.interned[description] = len(self.nodes)
            self.nodes.append(description)
        return self.interned[description]

    def succ(self, value):
        return self.node("s", value)

    @functools.cache
    def numeral(self, value):
        return self.zero if value == 0 else self.succ(self.numeral(value - 1))

    def iterator(self, count, seed, body):
        return self.node("i", count, seed, body)

    @functools.cache
    def shift(self, term, cutoff=0):
        entry = self.nodes[term]
        if entry[0] == "z":
            return term
        if entry[0] == "v":
            return self.node("v", entry[1] + (entry[1] >= cutoff))
        if entry[0] == "s":
            return self.succ(self.shift(entry[1], cutoff))
        _, count, seed, body = entry
        return self.iterator(self.shift(count, cutoff),
                             self.shift(seed, cutoff),
                             self.shift(body, cutoff + 1))

    def select(self, count, if_zero, if_nonzero):
        # Its update ignores the newly bound accumulator; lift outer indices.
        return self.iterator(count, if_zero, self.shift(if_nonzero))

    def zero_test(self, value):
        return self.select(value, self.one, self.zero)

    def xor(self, left, right):
        return self.select(left, right, self.zero_test(right))

    def boolean_or(self, left, right):
        return self.select(left, right, self.one)

    @functools.cache
    def free_scope(self, term):
        entry = self.nodes[term]
        if entry[0] == "z":
            return 0
        if entry[0] == "v":
            return entry[1] + 1
        if entry[0] == "s":
            return self.free_scope(entry[1])
        return max(self.free_scope(entry[1]), self.free_scope(entry[2]),
                   self.free_scope(entry[3]) - 1)

    def evaluate(self, term, environment):
        # Ignore unused outer variables so DAG sharing also shares evaluations.
        return self.evaluate_scoped(term, environment[:self.free_scope(term)])

    @functools.cache
    def evaluate_scoped(self, term, environment):
        entry = self.nodes[term]
        if entry[0] == "z":
            return 0
        if entry[0] == "v":
            return environment[entry[1]]
        if entry[0] == "s":
            return 1 + self.evaluate(entry[1], environment)
        _, count, seed, body = entry
        number_of_steps = self.evaluate(count, environment)
        value = self.evaluate(seed, environment)
        for _ in range(number_of_steps):
            value = self.evaluate(body, (value,) + environment)
        return value

    @functools.cache
    def tree_size(self, term):
        entry = self.nodes[term]
        if entry[0] in ("z", "v"):
            return 1
        return 1 + sum(self.tree_size(child) for child in entry[1:])

    def reachable_size(self, term):
        seen = set()
        pending = [term]
        while pending:
            current = pending.pop()
            if current in seen:
                continue
            seen.add(current)
            entry = self.nodes[current]
            if entry[0] not in ("z", "v"):
                pending.extend(entry[1:])
        return len(seen)


def generate_clocks(terms, maximum):
    bodies = {2: terms.zero_test(terms.var)}
    for period in range(2, maximum):
        old_body = bodies[period]
        clock = terms.iterator(terms.var, terms.zero, old_body)
        selection = terms.zero
        for phase in range(1, period):
            rotation = terms.iterator(terms.numeral(period - phase),
                                      clock, old_body)
            test = terms.zero_test(rotation)
            selection = terms.select(test, selection, terms.numeral(phase + 1))
        bodies[period + 1] = terms.select(terms.var, terms.one, selection)
    return bodies


def discriminator(terms, body, period, left, right):
    value = terms.zero
    for phase in range(period):
        count = terms.numeral((-phase) % period)
        a = terms.zero_test(terms.iterator(count, left, body))
        b = terms.zero_test(terms.iterator(count, right, body))
        value = terms.boolean_or(value, terms.xor(a, b))
    return value


def run(maximum, bound):
    terms = ScalarTerms()
    bodies = generate_clocks(terms, maximum)
    checks = 0
    rows = []

    def require(condition, message):
        nonlocal checks
        checks += 1
        if not condition:
            raise ValueError(message)

    for period, body in bodies.items():
        clock = terms.iterator(terms.var, terms.zero, body)
        rotated = terms.iterator(terms.numeral(period - 1), terms.var, body)
        diagonal = discriminator(terms, body, period, terms.var, terms.var)
        displaced = discriminator(terms, body, period, terms.var, rotated)
        for value in range(bound + 1):
            actual = terms.evaluate(body, (value,))
            require(0 <= actual < period, ("finite range", period, value, actual))
            require(terms.evaluate(clock, (value,)) == value % period,
                    ("bounded clock", period, value))
            require(terms.evaluate(diagonal, (value,)) == 0,
                    ("bounded diagonal", period, value))
        table = []
        for value in range(period):
            actual = terms.evaluate(body, (value,))
            table.append(actual)
            require(actual == (value + 1) % period,
                    ("cycle transition", period, value, actual))
            require(terms.evaluate(displaced, (value,)) == 1,
                    ("displaced discrimination", period, value))
        rows.append({"period": period, "cycle_table": table,
                     "update_tree_nodes_if_expanded": terms.tree_size(body),
                     "update_reachable_dag_nodes": terms.reachable_size(body)})

    return {"verification_scope": "Bounded standard-number evaluations only; "
             "not a formal verification or a proof of the universal theorem.",
            "term_primitives": ["variable", "zero", "successor", "scalar iterator"],
            "maximum_period": maximum, "maximum_test_input": bound,
            "successful_checks": checks, "failures": 0,
            "total_dag_nodes": len(terms.nodes), "clocks": rows}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-period", type=int, default=12)
    parser.add_argument("--max-input", type=int, default=32)
    args = parser.parse_args()
    if args.max_period < 2 or args.max_input < 0:
        parser.error("max-period must be at least 2 and max-input nonnegative")
    print(json.dumps(run(args.max_period, args.max_input), indent=2))

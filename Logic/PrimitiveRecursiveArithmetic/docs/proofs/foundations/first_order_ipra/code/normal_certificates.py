"""Finite resolution certificates and the relational existential-universal fragment.

Run this module directly for exhaustive two-atom tests and equality-sensitive
examples. The BSR input matrix is already in CNF. Nonnegative term indices
name constants, followed by existential witnesses; -1, -2, ... name the
universal variables. The same index may occur repeatedly in any relation.
"""
from dataclasses import dataclass
from itertools import product
from typing import Optional


Clause = frozenset[int]
GroundAtom = tuple[Optional[str], tuple[int, ...]]


@dataclass(frozen=True)
class Leaf:
    clause_index: int


@dataclass(frozen=True)
class Resolve:
    atom: int
    positive: "Proof"
    negative: "Proof"


Proof = Leaf | Resolve


def true_literal(literal: int, valuation: tuple[bool, ...]) -> bool:
    return valuation[abs(literal) - 1] == (literal > 0)


def solve(clauses: list[Clause], num_atoms: int) -> tuple[bool, ...] | Proof:
    """Return a satisfying assignment or an ordinary, unweakened resolution tree."""
    if num_atoms < 0 or any(not 1 <= abs(lit) <= num_atoms
                            for clause in clauses for lit in clause):
        raise ValueError("literal outside the declared range")
    for valuation in product((False, True), repeat=num_atoms):
        if all(any(true_literal(lit, valuation) for lit in c) for c in clauses):
            return valuation

    def derive(prefix: tuple[bool, ...]) -> tuple[Clause, Proof]:
        # Stop a branch early whenever an input clause is already falsified.
        for i, clause in enumerate(clauses):
            if all(abs(lit) <= len(prefix) and not true_literal(lit, prefix)
                   for lit in clause):
                return clause, Leaf(i)
        pivot = len(prefix) + 1
        if pivot > num_atoms:
            raise AssertionError("a full assignment passed the unsatisfiability scan")
        left, left_proof = derive(prefix + (False,))
        if pivot not in left:
            return left, left_proof
        right, right_proof = derive(prefix + (True,))
        if -pivot not in right:
            return right, right_proof
        return (left - {pivot}) | (right - {-pivot}), Resolve(pivot, left_proof, right_proof)

    result, proof = derive(())
    assert not result
    return proof


def conclusion(clauses: list[Clause], proof: Proof) -> Clause:
    """Reconstruct the conclusion independently; reject invalid leaves or pivots."""
    if isinstance(proof, Leaf):
        if not 0 <= proof.clause_index < len(clauses):
            raise ValueError("invalid leaf index")
        return clauses[proof.clause_index]
    if not isinstance(proof, Resolve) or proof.atom <= 0:
        raise ValueError("invalid pivot record")
    left = conclusion(clauses, proof.positive)
    right = conclusion(clauses, proof.negative)
    if proof.atom not in left or -proof.atom not in right:
        raise ValueError("opposite pivot literals are missing")
    return (left - {proof.atom}) | (right - {-proof.atom})


@dataclass(frozen=True)
class Literal:
    positive: bool
    relation: Optional[str]  # None represents logical equality.
    terms: tuple[int, ...]


@dataclass(frozen=True)
class Sentence:
    constants: int
    existentials: int
    universals: int
    relations: tuple[tuple[str, int], ...]
    matrix: tuple[tuple[Literal, ...], ...]

    @property
    def names(self) -> int:
        return max(1, self.constants + self.existentials)

    def validate(self) -> None:
        if min(self.constants, self.existentials, self.universals) < 0:
            raise ValueError("negative signature or prefix size")
        arities = dict(self.relations)
        if len(arities) != len(self.relations) or any(
            not isinstance(name, str) or arity < 0 for name, arity in self.relations
        ):
            raise ValueError("ill-formed relation signature")
        for clause in self.matrix:
            for lit in clause:
                if len(lit.terms) != (2 if lit.relation is None else arities.get(lit.relation, -1)):
                    raise ValueError("arity mismatch or unknown relation")
                if any(not -self.universals <= t < self.constants + self.existentials
                       for t in lit.terms):
                    raise ValueError("term outside the prefix")


def ground(sentence: Sentence) -> tuple[dict[GroundAtom, int], list[Clause]]:
    sentence.validate()
    labels: dict[GroundAtom, int] = {}
    clauses: list[Clause] = []
    names = range(sentence.names)

    def atom(relation: Optional[str], args: tuple[int, ...]) -> int:
        return labels.setdefault((relation, args), len(labels) + 1)

    def eq(i: int, j: int) -> int:
        return atom(None, (i, j))

    for i in names:
        clauses.append(frozenset([eq(i, i)]))
        for j in names:
            clauses.append(frozenset([-eq(i, j), eq(j, i)]))
            for k in names:
                clauses.append(frozenset([-eq(i, j), -eq(j, k), eq(i, k)]))
    for name, arity in sentence.relations:
        tuples = list(product(names, repeat=arity))
        for a in tuples:
            for b in tuples:
                clauses.append(frozenset([-eq(i, j) for i, j in zip(a, b)]
                                         + [-atom(name, a), atom(name, b)]))
    for y in product(names, repeat=sentence.universals):
        for row in sentence.matrix:
            clause = set()
            for lit in row:
                args = tuple(t if t >= 0 else y[-t - 1] for t in lit.terms)
                index = atom(lit.relation, args)
                clause.add(index if lit.positive else -index)
            clauses.append(frozenset(clause))
    return labels, clauses


@dataclass(frozen=True)
class Model:
    size: int
    named: tuple[int, ...]  # original constants and existential witnesses
    positive_relations: frozenset[tuple[str, tuple[int, ...]]]

    def satisfies(self, sentence: Sentence) -> bool:
        sentence.validate()
        if self.size < 1 or len(self.named) != sentence.constants + sentence.existentials:
            return False
        if any(not 0 <= a < self.size for a in self.named):
            return False
        arities = dict(sentence.relations)
        for name, args in self.positive_relations:
            if arities.get(name, -1) != len(args) or any(not 0 <= a < self.size for a in args):
                return False
        for y in product(range(self.size), repeat=sentence.universals):
            for clause in sentence.matrix:
                for lit in clause:
                    args = tuple(self.named[t] if t >= 0 else y[-t - 1] for t in lit.terms)
                    bit = args[0] == args[1] if lit.relation is None else (lit.relation, args) in self.positive_relations
                    if bit == lit.positive:
                        break
                else:
                    return False
        return True


def decide(sentence: Sentence) -> Model | Proof:
    labels, clauses = ground(sentence)
    result = solve(clauses, len(labels))
    if not isinstance(result, tuple):
        return result
    names = range(sentence.names)
    representatives = [next(j for j in names if result[labels[(None, (i, j))] - 1])
                       for i in names]
    domain = sorted(set(representatives))
    named = tuple(domain.index(i) for i in representatives)
    positive = set()
    for relation, arity in sentence.relations:
        for args in product(domain, repeat=arity):
            if result[labels[(relation, args)] - 1]:
                positive.add((relation, tuple(domain.index(a) for a in args)))
    return Model(len(domain), named[:sentence.constants + sentence.existentials], frozenset(positive))


def self_test() -> None:
    # Every subset of the nine non-tautological clauses on two atoms.
    possible = [frozenset(i * s for i, s in enumerate(digits, start=1) if s)
                for digits in product((-1, 0, 1), repeat=2)]
    sat_count = 0
    for mask in range(1 << len(possible)):
        clauses = [c for i, c in enumerate(possible) if mask & (1 << i)]
        answer = solve(clauses, 2)
        if isinstance(answer, tuple):
            assert all(any(true_literal(lit, answer) for lit in c) for c in clauses)
            sat_count += 1
        else:
            assert not conclusion(clauses, answer)
    # A bad purported proof cannot derive an empty clause.
    try:
        conclusion([frozenset([1])], Resolve(1, Leaf(0), Leaf(0)))
    except ValueError:
        pass
    else:
        raise AssertionError("invalid pivot accepted")

    def unit(sign: bool, name: Optional[str], *args: int) -> tuple[Literal, ...]:
        return (Literal(sign, name, args),)

    def example(sentence: Sentence, expected_size: Optional[int]) -> None:
        result = decide(sentence)
        if expected_size is None:
            assert not isinstance(result, Model)
            assert not conclusion(ground(sentence)[1], result)
        else:
            assert isinstance(result, Model) and result.size == expected_size
            assert result.satisfies(sentence)

    ps = (("P", 1),)
    example(Sentence(1, 1, 0, ps, (unit(True, None, 0, 1), unit(True, "P", 0))), 1)
    example(Sentence(2, 0, 0, ps, (unit(False, None, 0, 1),)), 2)
    example(Sentence(0, 2, 0, ps, (unit(True, None, 0, 1), unit(True, "P", 0),
                                      unit(False, "P", 1))), None)
    example(Sentence(0, 1, 1, ps, (unit(True, "P", 0), unit(False, "P", -1))), None)
    example(Sentence(0, 0, 1, ps, (unit(True, None, -1, -1),)), 1)
    example(Sentence(0, 0, 0, (("C", 0),), (unit(True, "C"),)), 1)
    example(Sentence(0, 0, 0, (), ((),)), None)
    example(Sentence(0, 0, 0, (), ()), 1)
    print(f"512 clause families: {sat_count} verified assignments, "
          f"{512 - sat_count} verified resolution refutations.")
    print("Eight Bernays–Schönfinkel examples passed: quotient models or checked refutations.")


if __name__ == "__main__":
    self_test()

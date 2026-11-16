"""Finite challenge-contract reference algorithms.

These are exact finite diagnostics, not Lean proofs or iPRA derivations.
Object matrices and function tables have explicit finite bounds. Query
subsets are canonical bitsets, so comparison ignores neither multiplicity
nor order accidentally: each subset has exactly one representation.
"""
from dataclasses import dataclass
from itertools import product
import json


@dataclass(frozen=True)
class Contract:
    witnesses: int
    questions: int
    relation: tuple

    def valid(self):
        return (self.witnesses >= 0 and self.questions >= 0
                and len(self.relation) == self.witnesses
                and all(len(row) == self.questions
                        and all(type(v) is bool for v in row)
                        for row in self.relation))

    def realizes(self, witness):
        return 0 <= witness < self.witnesses and all(self.relation[witness])


@dataclass(frozen=True)
class Hom:
    source: Contract
    target: Contract
    forward: tuple
    query: tuple  # query[x][target_question] is a source-question bitset

    def valid(self):
        a, b = self.source, self.target
        if not a.valid() or not b.valid():
            return False
        if len(self.forward) != a.witnesses or len(self.query) != a.witnesses:
            return False
        if any(not 0 <= v < b.witnesses for v in self.forward):
            return False
        for x, row in enumerate(self.query):
            if len(row) != b.questions:
                return False
            for v, bits in enumerate(row):
                if not 0 <= bits < (1 << a.questions):
                    return False
                antecedent = all(a.relation[x][u] for u in range(a.questions)
                                 if bits & (1 << u))
                if antecedent and not b.relation[self.forward[x]][v]:
                    return False
        return True


def identity(a):
    return Hom(a, a, tuple(range(a.witnesses)),
               tuple(tuple(1 << u for u in range(a.questions))
                     for _ in range(a.witnesses)))


def compose(g, f):
    assert f.target == g.source and f.valid() and g.valid()
    a, b, c = f.source, f.target, g.target
    rows = []
    for x in range(a.witnesses):
        row = []
        for w in range(c.questions):
            bits = 0
            for v in range(b.questions):
                if g.query[f.forward[x]][w] & (1 << v):
                    bits |= f.query[x][v]
            row.append(bits)
        rows.append(tuple(row))
    return Hom(a, c, tuple(g.forward[f.forward[x]] for x in range(a.witnesses)),
               tuple(rows))


def all_homs(a, b):
    answer = []
    for f in product(range(b.witnesses), repeat=a.witnesses):
        for flat in product(range(1 << a.questions),
                            repeat=a.witnesses * b.questions):
            rows = tuple(tuple(flat[x * b.questions + v]
                               for v in range(b.questions))
                         for x in range(a.witnesses))
            h = Hom(a, b, f, rows)
            if h.valid():
                answer.append(h)
    return tuple(answer)


def contract_product(a, b):
    return Contract(a.witnesses * b.witnesses, a.questions + b.questions,
                    tuple(a.relation[x] + b.relation[y]
                          for x in range(a.witnesses)
                          for y in range(b.witnesses)))


def projections(a, b):
    p = contract_product(a, b)
    fst = Hom(p, a,
              tuple(x for x in range(a.witnesses) for _ in range(b.witnesses)),
              tuple(tuple(1 << u for u in range(a.questions))
                    for _ in range(p.witnesses)))
    snd = Hom(p, b,
              tuple(y for _ in range(a.witnesses) for y in range(b.witnesses)),
              tuple(tuple(1 << (a.questions + v) for v in range(b.questions))
                    for _ in range(p.witnesses)))
    return fst, snd


def pairing(f, g):
    assert f.source == g.source and f.valid() and g.valid()
    a, b, c = f.target, g.target, f.source
    return Hom(c, contract_product(a, b),
               tuple(f.forward[x] * b.witnesses + g.forward[x]
                     for x in range(c.witnesses)),
               tuple(f.query[x] + g.query[x] for x in range(c.witnesses)))


def check():
    objects = (
        Contract(0, 0, ()),
        Contract(1, 0, ((),)),
        Contract(1, 1, ((True,),)),
        Contract(1, 1, ((False,),)),
        Contract(2, 1, ((False,), (True,))),
    )
    homs = {(a, b): all_homs(a, b) for a in objects for b in objects}
    counts = {"objects": len(objects), "arrows": sum(map(len, homs.values())),
              "composition_checks": 0, "associativity_checks": 0,
              "product_pairings": 0, "product_eta_checks": 0,
              "realization_transports": 0}
    for a in objects:
        assert identity(a).valid()
        for b in objects:
            for f in homs[a, b]:
                assert compose(identity(b), f) == f
                assert compose(f, identity(a)) == f
                for x in range(a.witnesses):
                    if a.realizes(x):
                        assert b.realizes(f.forward[x])
                        counts["realization_transports"] += 1
                for c in objects:
                    for g in homs[b, c]:
                        assert compose(g, f).valid()
                        counts["composition_checks"] += 1
                        for d in objects:
                            for h in homs[c, d]:
                                assert compose(h, compose(g, f)) == compose(compose(h, g), f)
                                counts["associativity_checks"] += 1
    # Pairing laws over all small original-object maps. This includes empty
    # witnesses/questions; product objects need not be in the original list.
    for a in objects:
        for b in objects:
            p, q = projections(a, b)
            assert p.valid() and q.valid()
            for c in objects:
                for f in homs[c, a]:
                    for g in homs[c, b]:
                        paired = pairing(f, g)
                        assert paired.valid()
                        assert compose(p, paired) == f
                        assert compose(q, paired) == g
                        counts["product_pairings"] += 1
                # Exhaustive eta checks are finite, including 2x2 targets.
                for k in all_homs(c, contract_product(a, b)):
                    assert pairing(compose(p, k), compose(q, k)) == k
                    counts["product_eta_checks"] += 1
    return counts


if __name__ == "__main__":
    print(json.dumps(check(), indent=2, sort_keys=True))

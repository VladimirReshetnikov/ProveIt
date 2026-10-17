#!/usr/bin/env python3
"""Exhaustive finite countermodels for three single-row deletions of FC15.

Independent semantic checker for the nine-function, guard-fused payload.
The finite models certify failure of the weakened target, not consistency
or inconsistency of the complete FC15 theory. No external libraries used.
"""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path


class Model:
    def __init__(self, deleted: int):
        if deleted not in (1, 2, 5):
            raise ValueError("only the three proved countermodels are implemented")
        self.deleted = deleted
        self.domain = (0,) if deleted == 5 else (0, 1, 2)
        self.d = 0

    def E(self, x, y):
        return True if self.deleted == 5 else (x, y) in ((2, 1), (1, 2))

    def Inc(self, s, t):
        return True if self.deleted == 5 else t == 1

    def G(self, b, t):
        return True if self.deleted == 5 else t != 1

    def V(self, s, j):
        return s if self.deleted == 2 else 0

    def C(self, s, j, z):
        return z if self.deleted == 2 else s

    def N(self, a, b):
        return 0 if self.deleted == 5 or a == b == 1 else 1

    def A(self, j, k):
        return 0

    def Q(self, j, a):
        return a

    def W(self, s, j, a):
        return 0

    def H(self, b, t):
        return 0

    def Y(self, b, t, u):
        return 0 if self.deleted == 5 else (1, 2, 1)[u]

    def Z(self, b, t, u):
        return 0 if self.deleted == 5 else (2, 1, 2)[u]

    def D(self, x):
        # This is an abbreviation, not a retained proper function symbol.
        return self.W(self.C(self.d, self.q, x), self.d, self.A(self.d, self.q))

    @property
    def q(self):
        return self.N(self.d, self.d)

    def R(self, b, t, x, y):
        return self.Inc(self.C(self.C(b, self.d, x), self.q, y), t)


def clauses(m):
    """Rows are expanded semantically; q and R use their exact definitions."""
    return [
        (("s", "j", "z"), lambda s, j, z: m.V(m.C(s, j, z), j) == z),
        (("s", "j", "z", "k"),
         lambda s, j, z, k: k == j or m.V(m.C(s, j, z), k) == m.V(s, k)),
        (("s", "a", "b"), lambda s, a, b: m.Inc(s, m.N(a, b)) or m.Inc(s, a)),
        (("s", "a", "b"), lambda s, a, b: m.Inc(s, m.N(a, b)) or m.Inc(s, b)),
        (("s", "a", "b"), lambda s, a, b:
         not m.Inc(s, m.N(a, b)) or not m.Inc(s, a) or not m.Inc(s, b)),
        (("s", "j", "k"), lambda s, j, k:
         not m.Inc(s, m.A(j, k)) or m.E(m.V(s, j), m.V(s, k))),
        (("s", "j", "k"), lambda s, j, k:
         m.Inc(s, m.A(j, k)) or not m.E(m.V(s, j), m.V(s, k))),
        (("s", "j", "a", "z"), lambda s, j, a, z:
         not m.Inc(m.C(s, j, z), a) or m.Inc(s, m.Q(j, a))),
        (("s", "j", "a"), lambda s, j, a:
         not m.Inc(s, m.Q(j, a)) or m.Inc(m.C(s, j, m.W(s, j, a)), a)),
        (("b", "t", "u"), lambda b, t, u:
         m.G(b, t) or m.R(b, t, m.H(b, t), m.Y(b, t, u))),
        (("b", "t", "u"), lambda b, t, u:
         m.G(b, t) or m.E(m.Z(b, t, u), m.Y(b, t, u))),
        (("b", "t", "u"), lambda b, t, u:
         m.G(b, t) or not m.E(m.Z(b, t, u), u)),
        (("b", "t", "x", "y"), lambda b, t, x, y:
         not m.G(b, t) or not m.E(x, m.H(b, t)) or not m.R(b, t, x, y)
         or m.E(y, m.H(b, t))),
        (("b", "t", "x", "y"), lambda b, t, x, y:
         not m.G(b, t) or m.E(m.D(x), x) or not m.R(b, t, x, y)
         or m.E(y, m.H(b, t))),
        (("b", "t", "y"), lambda b, t, y:
         not m.G(b, t) or not m.E(y, m.H(b, t)) or m.R(b, t, m.Y(b, t, y), y)),
    ]


def audit(deleted):
    m = Model(deleted)
    rows = []
    total = 0
    for number, (variables, evaluate) in enumerate(clauses(m), 1):
        failures = []
        checked = 0
        for values in itertools.product(m.domain, repeat=len(variables)):
            checked += 1
            if not evaluate(*values):
                failures.append(dict(zip(variables, values)))
        rows.append({"clause": number, "assignments": checked,
                     "failure_count": len(failures), "first_failures": failures[:3]})
        total += checked
        if number == deleted:
            assert failures, "negative control: the deleted row must fail"
        else:
            assert not failures, (deleted, number, failures[:1])

    # The two three-object E-reducts even satisfy Extensionality.  A witness
    # can be chosen from the finite symmetric difference of any unequal pair.
    extensionally_distinct = all(
        a == b or any(m.E(x, a) != m.E(x, b) for x in m.domain)
        for a, b in itertools.product(m.domain, repeat=2)
    )
    assert extensionally_distinct
    return {
        "deleted_clause": deleted,
        "domain": list(m.domain),
        "d": m.d,
        "q": m.q,
        "E": [[x, y] for x, y in itertools.product(m.domain, repeat=2) if m.E(x, y)],
        "Inc": [[x, y] for x, y in itertools.product(m.domain, repeat=2) if m.Inc(x, y)],
        "total_assignments": total,
        "all_retained_rows_hold": True,
        "deleted_row_fails": True,
        "extensional_E_reduct": extensionally_distinct,
        "rows": rows,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = {"theory": "FC15* guard-fused nine-function universal theory with derived member term",
              "status": "PASS",
              "scope": "exact finite models of three individually weakened theories",
              "countermodels": [audit(i) for i in (1, 2, 5)]}
    payload = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(payload, encoding="utf-8")
        print(json.dumps({"status": "PASS", "output": str(args.output),
                          "models": 3,
                          "total_clause_assignments": sum(x["total_assignments"]
                                                          for x in result["countermodels"])}))
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()

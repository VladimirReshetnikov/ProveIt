"""Count a fully expanded inherited universal-macro family.

This is a syntax audit, not a theorem checker. Formula constructors are
Eq and D only. All variables introduced by the builder have unique names.
"""

import json
from itertools import count
from pathlib import Path

from pred50 import ZERO, add, predecessor50, predecessor57, select, size, suc, var

names = count()


def fresh():
    return "macro_" + str(next(names))


def replace_term(t, name, value):
    if t[0] == "v":
        return value if t[1] == name else t
    if t[0] == "0":
        return t
    if t[0] == "S":
        return ("S", replace_term(t[1], name, value))
    return ("I", replace_term(t[1], name, value),
            replace_term(t[2], name, value), t[3],
            t[4] if t[3] == name else replace_term(t[4], name, value))


def replace_formula(a, name, value):
    if a[0] == "Eq":
        return ("Eq", replace_term(a[1], name, value),
                replace_term(a[2], name, value))
    return a if name in a[1:3] else (
        "D", a[1], a[2], replace_formula(a[3], name, value))


def gate(z, a):
    if a[0] == "Eq":
        return ("Eq", select(z, ZERO, a[1]), select(z, ZERO, a[2]))
    return ("D", a[1], a[2], gate(z, a[3]))


def universal(name, a, predecessor):
    unused, z = fresh(), fresh()
    replaced = replace_formula(a, name, predecessor(var(z)))
    return ("D", unused, z, gate(var(z), replaced))


def formula_size(a):
    if a[0] == "Eq":
        return 1 + size(a[1]) + size(a[2])
    return 1 + formula_size(a[3])


def family(n, predecessor):
    value = ZERO
    for j in range(n):
        value = add(value, var("x" + str(j)))
    a = ("Eq", value, suc(ZERO))
    for j in reversed(range(n)):
        a = universal("x" + str(j), a, predecessor)
    return a


def main():
    rows = []
    for n in range(9):
        old = formula_size(family(n, predecessor57))
        new = formula_size(family(n, predecessor50))
        if (old, new) != (67 * n + 4, 60 * n + 4):
            raise ValueError((n, old, new))
        rows.append({"quantifiers": n, "with_pred57": old,
                     "with_pred50": new, "saved_nodes": old - new})
    result = {"scope": "Raw Eq/D formula tree before guarded public translation",
              "old_formula": "67*n+4", "new_formula": "60*n+4", "rows": rows}
    destination = Path(__file__).resolve().parents[2] / "evidence"
    destination.mkdir(exist_ok=True)
    (destination / "universal_sizes.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()

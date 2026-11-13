"""Exhaust all raw unary 0/S/I terms through nine nodes, without cutoffs.

This finite enumeration supplements the analytic bound in the report.
Variables use de Bruijn indices; entering an iterator body prepends its state.
The zero constant and every available variable each count as one node.
"""
from functools import cache
from itertools import product
from pathlib import Path
import json

@cache
def terms(size, variables):
    if size == 1:
        return (("zero",),) + tuple(("var", i) for i in range(variables))
    result = [("suc", t) for t in terms(size - 1, variables)]
    for n_size in range(1, size - 2):
        for a_size in range(1, size - n_size - 1):
            h_size = size - 1 - n_size - a_size
            if h_size > 0:
                result.extend(("it", n, a, h) for n, a, h in product(
                    terms(n_size, variables), terms(a_size, variables),
                    terms(h_size, variables + 1)))
    return tuple(result)

@cache
def evaluate(t, env):
    tag = t[0]
    if tag == "zero":
        return 0
    if tag == "var":
        return env[t[1]]
    if tag == "suc":
        return evaluate(t[1], env) + 1
    n, value = evaluate(t[1], env), evaluate(t[2], env)
    for _ in range(n):
        value = evaluate(t[3], (value,) + env)
    return value

def main():
    rows, witnesses = [], []
    for size in range(1, 10):
        hits = []
        candidates = terms(size, 1)
        for t in candidates:
            a = evaluate(t, (0,))
            b = evaluate(t, (a,))
            c = evaluate(t, (b,))
            if a > 0 and b > 0 and a != b and c == 0:
                hits.append({"tree": t, "cycle": [0, a, b, 0]})
        rows.append({"nodes": size, "trees": len(candidates),
                     "three_cycles_through_zero": len(hits)})
        if hits:
            witnesses.extend(hits)
        evaluate.cache_clear()
    assert sum(r["trees"] for r in rows[:-1]) == 3160
    assert all(r["three_cycles_through_zero"] == 0 for r in rows[:-1])
    assert rows[-1] == {"nodes": 9, "trees": 8738,
                        "three_cycles_through_zero": 1}
    expected = ("it", ("suc", ("var", 0)), ("var", 0),
                ("it", ("var", 0), ("suc", ("var", 1)), ("zero",)))
    assert witnesses[0]["tree"] == expected
    report = {"status": "passed", "rows": rows, "witnesses": witnesses,
              "cutoffs": "none", "skipped_candidates": 0,
              "scope": "Raw unary terms, at most nine nodes, exact evaluation"}
    Path(__file__).with_name("clock_minimum_results.json").write_text(
        json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))

if __name__ == "__main__":
    main()

import itertools
import json
import random
import time
from pathlib import Path
from dualforest.reductions import cnf_instance
from dualforest.dependencies import columns, peel
from dualforest import solve, verify_positive, verify_negative


def run():
    rng = random.Random(120626)
    t = time.perf_counter()
    assignments = 0
    formula_count = 0
    for _ in range(400):
        v = rng.randint(1, 6)
        clauses = [[rng.choice([-1, 1])*rng.randint(1, v) for _ in range(rng.randint(0, 4))]
                   for _ in range(rng.randint(1, 7))]
        inst, meta = cnf_instance(v, clauses)
        assert max(map(len, columns(inst).values())) <= 3
        for values in itertools.product((False, True), repeat=v):
            expected = all(any(values[abs(l)-1] == (l > 0) for l in c) for c in clauses)
            tree = [2*i + (not value) for i, value in enumerate(values)]
            assert (peel(inst, tree) is not None) == expected
            assignments += 1
        formula_count += 1
    exact_count = 0
    for _ in range(40):
        v = rng.randint(1, 3)
        clauses = [[rng.choice([-1, 1])*rng.randint(1, v) for _ in range(3)] for _ in range(3)]
        inst, _ = cnf_instance(v, clauses)
        expected = any(all(any(values[abs(l)-1] == (l > 0) for l in c) for c in clauses)
                       for values in itertools.product((False, True), repeat=v))
        ans = solve(inst, try_incumbent=False)
        assert (ans['status'] == 'yes') == expected
        if expected:
            assert verify_positive(inst, ans['certificate'])
        else:
            assert verify_negative(inst, ans['negative_certificate'])
        exact_count += 1
    result = dict(formulas=formula_count, assignments=assignments,
                  additional_exact_solver_formulas=exact_count, mismatches=0,
                  seconds=time.perf_counter()-t,
                  scope='Synthetic CNF-to-matrix reduction; no geometric realization asserted.')
    (Path(__file__).resolve().parents[1]/'results'/'sat_audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    run()

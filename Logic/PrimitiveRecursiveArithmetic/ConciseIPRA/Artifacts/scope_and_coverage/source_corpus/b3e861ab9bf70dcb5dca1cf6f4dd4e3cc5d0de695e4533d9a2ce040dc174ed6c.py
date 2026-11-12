"""Reproduce finite diagnostics for the proposed arithmetic core."""
import itertools
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'code'))
from selfseed_model import (F, D, band, bor, bnot, V, W,
                           predecessor_graph_value, C, L, Sel,
                           clip_shifted, run_shifted)


def main():
    counts = {}

    def check(name, condition):
        if not condition:
            raise AssertionError(name)
        counts[name] = counts.get(name, 0) + 1

    for a, b in itertools.product(range(2), repeat=2):
        check('Boolean conjunction', band(a, b) == (a & b))
        check('Boolean disjunction', bor(a, b) == (a | b))
        check('Boolean negation', bnot(a) == 1-a)
    for a in range(20):
        for n in range(20):
            check('constant-body source equations', F(n, lambda v: a) == D(n, a))
            check('predecessor invariant', a == 1 or V(n, a) == n+2 or V(n, a)+1 == a)
            check('capped-count invariant', C(n, a) in (n+2, a+2))
            check('capped-count value', C(n, a) == min(n, a)+2)
            check('capped-count factor', C(n+1, a+1) == C(n, a)+1)
            check('comparison recurrence', L(a+1, n+1) == L(a, n))
            check('comparison value', L(a, n) == int(a <= n))
            check('unilateral comparison law', bool(L(a, n+1)) == bool(L(a, n) or a == n+1))
    for a in range(40):
        check('finite-case predecessor', predecessor_graph_value(a) == max(a-1, 0))
        check('tail predecessor', W(a+3) == a+2)
    check('small W values', [W(n) for n in range(3)] == [2, 2, 4])
    for bound in range(2, 10):
        for a, d, control in itertools.product(range(2, bound+1), range(2, bound+1), range(2)):
            check('bounded selector', Sel(bound, control, a, d) == (a if control else d))
        for a in range(2, 18):
            check('encoded clipping', clip_shifted(bound, a) == min(a, bound))
        # All finite state maps on these two/three-element intervals have
        # explicit finite equality-case source descriptions. Test all maps
        # when feasible and deterministic samples for the larger intervals.
        states = list(range(2, bound+1))
        tables = list(itertools.product(states, repeat=len(states))) if bound <= 4 else [
            tuple(states), tuple(reversed(states)), tuple([2]*len(states)),
            tuple([bound]*len(states)), tuple(min(v+1, bound) for v in states)]
        for table in tables:
            def update(v, table=table, bound=bound):
                return table[v-2] if 2 <= v <= bound else bound+7
            for initial in states:
                expected = initial
                for n in range(7):
                    check('two-sentinel bounded iteration', run_shifted(bound, n+2, initial, update) == expected)
                    expected = update(expected)
    result = {'status': 'passed', 'checks': counts, 'total': sum(counts.values()),
              'scope': 'Finite standard-natural-number diagnostics only; not a soundness or bi-interpretability proof.'}
    (ROOT / 'evidence' / 'selfseed_model_checks.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()

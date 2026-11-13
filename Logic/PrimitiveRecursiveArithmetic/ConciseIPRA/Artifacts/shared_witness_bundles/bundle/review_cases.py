"""Focused independent tests of named binding and shared-witness transport."""

import json
from pathlib import Path

from bundle_checker import accepts, falpha, ffree, fsub, talpha, tfree, tsub
from bundle_examples import induction_example, iterator, succ, transport


def run():
    results = {}
    t = iterator(0, 0, 2, iterator(2, 1, 2, 1))
    a = tsub(t, {1: 2})
    b = iterator(0, 0, 10, iterator(10, 2, 11, 2))
    results['nested_shadowed_term_capture'] = talpha(a) == talpha(b) and tfree(a) == {2}

    a = ['d', 1, [[2, ['=', 3, 1]], [4, ['q', 1, ['=', 3, 1]]]]]
    a = fsub(a, {3: 1})
    b = ['d', 10, [[20, ['=', 1, 10]], [40, ['q', 30, ['=', 1, 30]]]]]
    results['shared_outer_and_nested_formula_capture'] = falpha(a) == falpha(b) and ffree(a) == {1}

    doc = [['=', iterator(0, 0, 2, 2), 0],
           ['e', 0, iterator(0, 0, 9, 9), ['r', 0]]]
    results['alpha_comparison_root_expansion'] = accepts(doc)

    goal, proof = induction_example()
    proof[1][2] = 1
    results['eigenparameter_may_reuse_bound_name'] = accepts([goal, proof])

    a = ['d', 1, [[2, ['=', 2, 2]]]]
    proof = ['d', a, 0, [[2, 'c', ['r', succ(2)]]]]
    results['case_parameter_may_reuse_local_bound_name'] = accepts([a, proof])

    s = iterator(0, 2, 3, 3)
    h = iterator(1, 0, 2, 1)
    hs, ht = tsub(h, {1: s}), tsub(h, {1: 2})
    major = ['e', 0, s, ['r', 2]]
    proof = transport(s, 2, 1, h, hs, major, ['r', hs], scope={2})
    results['transport_substitution_capture_inside_iterator'] = accepts([['=', hs, ht], proof])

    Path(__file__).with_name('independent_audit.json').write_text(json.dumps(results, indent=2) + '\n')
    if not all(results.values()):
        raise RuntimeError(results)
    print(json.dumps(results, indent=2))


if __name__ == '__main__':
    run()

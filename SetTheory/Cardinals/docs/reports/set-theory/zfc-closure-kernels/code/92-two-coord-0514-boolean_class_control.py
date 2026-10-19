#!/usr/bin/env python3
"""FC13B/FC14B: cancel one class-level double negation in the FC13S hull.

This changes only the closure clause's I/U class expression.  It asserts no
equality of class objects and performs no rewrite in selector, V, C, or A-label
positions.  Under the common first twelve clauses the old and new closure
clauses are equivalent.  The resulting finite theories therefore have exactly
the same models, in the same signature, as their corresponding S variants.
"""
from __future__ import annotations
from itertools import product
import json
from pathlib import Path
import frozen_kernel as K
import frozen_frontend as F


def source_clauses(extensional=False):
    clauses = K.reduced_witness_clauses(extensional, True)
    sign, predicate, base, old_closure = clauses[12][-1]
    assert sign and predicate == 'Inc' and old_closure[0] == 'I'
    locally_bounded, old_hull = old_closure[1:]
    assert old_hull[0] == 'I' and old_hull[2] == K.d
    universal = old_hull[1]
    assert universal[0] == 'U'
    selector, negated_conjunction = universal[1:]
    assert negated_conjunction[0] == 'I' and negated_conjunction[2] == K.d
    conjunction = negated_conjunction[1]
    assert conjunction[0] == 'I' and conjunction[2] == K.d
    # conjunction = I(X,d), negated_conjunction = I(I(X,d),d).
    # X = I(closed,I(supported,d)); the universally quantified matrix alone
    # is replaced by X.  No class-object equality is inferred from Inc.
    inner = conjunction[1]
    assert inner[0] == 'I' and inner[2][0] == 'I' and inner[2][2] == K.d
    new_hull = K.f('I', K.f('U', selector, inner), K.d)
    new_closure = K.f('I', locally_bounded, new_hull)
    clauses[12][-1] = (sign, predicate, base, new_closure)
    return clauses


def regressions():
    imply = lambda p,q:(not p) or q
    tested = 0
    # All possible class truth values along nonempty finite quantifier fibers;
    # this is an algebraic identity check, not a model of the infinite core.
    for size in range(1, 5):
        for values in product((False,True), repeat=2*size):
            closed, support = values[:size], values[size:]
            old_matrix = [imply(imply(imply(c,imply(s,False)),False),False)
                          for c,s in zip(closed,support)]
            new_matrix = [imply(c,imply(s,False)) for c,s in zip(closed,support)]
            assert old_matrix == new_matrix
            old_hull = imply(all(old_matrix), False)
            new_hull = imply(all(new_matrix), False)
            assert old_hull == new_hull == any(c and s for c,s in zip(closed,support))
            for bounded in (False,True):
                assert imply(bounded,old_hull) == imply(bounded,new_hull)
                tested += 1
    return {'finite_boolean_fiber_checks':tested,
            'scope':'propositional/quantifier identity; finite carriers are not full-core models'}


def main():
    import linear_ground_codec as L
    directory = Path(__file__).parent
    result = {'scope':'same-signature core-relative equivalent Boolean-normalized finite theories; no TM state bound',
              'regressions':regressions(), 'metrics':{}, 'stage_one':{}}
    for extensional in (False,True):
        name = 'FC14B' if extensional else 'FC13B'
        for complete in (False,True):
            suffix = '_complete' if complete else '_native'
            clauses = source_clauses(extensional)+(K.equality_clauses(F.FUNCS) if complete else [])
            old = K.reduced_witness_clauses(extensional,True)+(K.equality_clauses(F.FUNCS) if complete else [])
            metrics = K.metrics(clauses)
            assert K.metrics(old)['bits']-metrics['bits'] == 16
            assert K.metrics(old)['term_nodes']-metrics['term_nodes'] == 4
            result['metrics'][name+suffix] = metrics
            (directory/(name+suffix+'.json')).write_text(json.dumps(clauses,indent=2)+'\n')
            payload = K.pack(clauses)
            for bad in (payload[:-1],payload+'0'):
                try:
                    K.unpack(bad)
                except ValueError:
                    pass
                else:
                    raise AssertionError('malformed B payload accepted')
            (directory/(name+suffix+'.bits')).write_text(payload+'\n')
        clauses = source_clauses(extensional)+K.equality_clauses(F.FUNCS)
        ground, stats = L.ground_stage([K.d, K.f('V',K.d,K.d)], extensional, True, clauses)
        valuation = F.decide(ground)
        assert valuation is not None and F.check_valuation(ground, valuation)
        stats['result'] = 'SAT'; stats['witness_literals'] = len(valuation)
        result['stage_one'][name] = stats
    (directory/'boolean-class-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()

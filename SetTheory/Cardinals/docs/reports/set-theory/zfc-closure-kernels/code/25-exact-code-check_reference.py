#!/usr/bin/env python3
"""Independent semantic and negative checks for the two axiom constructors.

This tests the executable specification. It is not a theorem about Python,
an unbounded search, or a binary Turing-machine implementation.
"""
from __future__ import annotations
import argparse
from itertools import product
import json
from pathlib import Path
import reference_kernel as k
from finite_hulls import analyze, profiles


def truth(a, e, env):
    if a == k.BOT:
        return False
    if a[0] == 'mem':
        return bool(e[env[a[2]]] & (1 << env[a[1]]))
    if a[0] == 'imp':
        return not truth(a[1], e, env) or truth(a[2], e, env)
    if a[0] == 'all':
        return all(truth(a[2], e, {**env, a[1]: x}) for x in range(len(e)))
    raise ValueError('unexpected formula')


def direct_instance(matrix, e, env):
    r = []
    for x in range(len(e)):
        r.append(sum((1 << y) for y in range(len(e))
                     if truth(matrix, e, {**env, 0:x, 1:y})))
    return analyze(e, tuple(r))


def direct_schema(matrix, e, kernel):
    parameters = sorted(k.free(matrix) - {0, 1})
    for values in product(range(len(e)), repeat=len(parameters)):
        result = direct_instance(matrix, e, dict(zip(parameters, values)))
        witnesses = result['efpc_witnesses' if kernel == 'EFPC' else 'epsc_witnesses']
        if result['local_bound'] and not witnesses:
            return False
    return True


def profile_eq(i, j, witness=8):
    a, b = k.Mem(witness,i), k.Mem(witness,j)
    return k.All(witness,k.And(k.Imp(a,b),k.Imp(b,a)))


def run():
    atoms = [k.BOT] + [k.Mem(i,j) for i in range(3) for j in range(3)]
    matrices = atoms + [k.Not(a) for a in atoms]
    matrices += [k.Imp(a,b) for a in atoms[:5] for b in atoms[:5]]
    matrices += [k.All(i,a) for i in range(3) for a in atoms]
    matrices = list(dict.fromkeys(matrices))
    schema_checks = 0
    for n in (1,2):
        for e_code in range(1 << (n*n)):
            e = profiles(n, e_code)
            for matrix in matrices:
                for name, build in [('EPSC', k.epsc), ('EFPC', k.efpc)]:
                    assert truth(build(matrix), e, {}) == direct_schema(matrix,e,name)
                    assert not k.free(build(matrix))
                    schema_checks += 1

    # Capturing 1 by the existing binder would produce a different formula.
    a = k.All(1,k.Mem(0,1))
    renamed = k.replace_free(a,{0:1})
    assert renamed == k.All(2,k.Mem(1,2))
    substitution_checks = 0
    for n in (1,2):
        for e_code in range(1 << (n*n)):
            e = profiles(n,e_code)
            for a in matrices:
                for x,y in product(range(3),repeat=2):
                    replaced = k.replace_free(a,{x:y})
                    support = sorted(k.free(a) | k.free(replaced) | {x,y})
                    for values in product(range(n),repeat=len(support)):
                        env = dict(zip(support,values))
                        expected = truth(a,e,{**env,x:env[y]})
                        assert truth(replaced,e,env) == expected
                        substitution_checks += 1

    good = [
        ['UI',0,1, ['all',1,['mem',0,1]]],
        ['GEN',3,0],
        ['AX',['mem',0,1]],
    ]
    for name in ('EPSC','EFPC'):
        checked = k.check(good,name)
        assert checked['valid'] and not checked['refutation']

    invalid = [[], [['MP',0,0]], [['GEN',0,0]], [['AX']],
               [['IR']], [['EPSC',['bot']]], [['EFPC',['bot']]],
               [['QD',0,['mem',0,1],['bot']]],
               [['AX',['mem',-1,0]]], [['AX',['all',0]]],
               [['AX',['arbitrary','bottom']]],
               [['K',['bot'],['bot']],['MP',0,0]],
               [['UI',True,0,['bot']]]]
    for case in invalid:
        try:
            k.check(case)
        except ValueError:
            pass
        else:
            raise AssertionError(('invalid certificate accepted',case))

    # The pointwise gap is definable using equality-free formulas and parameters.
    e=(0,3,5)
    matrix=k.Or(k.And(profile_eq(0,2),profile_eq(1,2)),
                k.And(profile_eq(0,4),profile_eq(1,3)))
    instance=direct_instance(matrix,e,{2:0,3:1,4:2})
    assert instance['local_bound'] and instance['epsc_witnesses']==[1]
    assert not instance['efpc_witnesses']

    # Gate the relation so the universally closed EPSC axiom also holds.
    # The only active parameter valuations are (0,1,2) and its 1/2 mirror.
    empty = lambda i: k.All(8,k.Not(k.Mem(8,i)))
    gate = k.And(empty(2),k.And(k.Not(empty(3)),
                 k.And(k.Not(empty(4)),k.Not(profile_eq(3,4)))))
    gated = k.And(gate,matrix)
    failing_valuations=[]
    for values in product(range(3),repeat=3):
        result=direct_instance(gated,e,dict(zip((2,3,4),values)))
        assert result['local_bound'] and result['epsc_witnesses']
        if not result['efpc_witnesses']:
            failing_valuations.append(list(values))
    assert failing_valuations == [[0,1,2],[0,2,1]]
    assert truth(k.epsc(gated),e,{}) and direct_schema(gated,e,'EPSC')
    assert not truth(k.efpc(gated),e,{}) and not direct_schema(gated,e,'EFPC')

    # The printed abbreviated modal list lacks the reflexivity axiom T.
    imp=lambda a,b:not a or b
    box=lambda a:True
    diamond=lambda a:False
    modal_cases=0
    for a,b in product((False,True),repeat=2):
        assert imp(box(imp(a,b)),imp(box(a),box(b)))
        assert imp(diamond(a),box(diamond(a)))
        assert imp(diamond(diamond(a)),diamond(diamond(a)))
        assert imp(diamond(box(a)),box(diamond(a)))
        modal_cases+=4
    assert not imp(box(False),False)
    assert not imp(True,diamond(True))
    assert json.loads((Path(__file__).resolve().parent.parent /
                      'examples/valid_nonrefutation.json').read_text()) == good
    return dict(scope='Finite specification regressions, not a machine proof.',
                distinct_matrices=len(matrices),schema_semantic_checks=schema_checks,
                substitution_semantic_checks=substitution_checks,
                rejected_certificates=len(invalid),valid_nonrefutation_examples=2,
                parameter_definable_pointwise_counterexample=True,
                gated_parameter_valuations_checked=27,
                gated_universally_closed_epsc_holds=True,
                gated_efpc_failing_valuations=failing_valuations,
                modal_degenerate_axiom_checks=modal_cases,modal_T_fails=True,
                example_fixture_matches=True)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path)
    args=p.parse_args()
    text=json.dumps(run(),indent=2)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')


if __name__=='__main__':main()

"""Generate and check native proof certificates, including symbolic coverage.

The proof builder is untrusted.  Every accepted example is checked by the
standalone raw eight-rule kernel.  This verifies the displayed instances,
not the universal completeness metatheorem or the full predecessor proof.
"""
import copy
import json
from pathlib import Path
import checker_native as k

ROOT = Path(__file__).resolve().parents[1]


def S(a):
    return ['s', a]


def I(n, a, h):
    return ['i', n, a, h]


def eq(a, b):
    return ['=', a, b]


def C(n, a, b):
    return I(n, a, k.shift(b, 1))


def refl(t):
    z = ['zero', t, 1]
    return ['tr', 1, z, z]


def sym(p, left):
    return ['tr', 1, refl(left), p]


def trans(p, q, left):
    return ['tr', 1, q, sym(p, left)]


def normalize_with_proof(t):
    """Reduce only exposed computations; return a term and a kernel proof."""
    if type(t) is int:
        return t, refl(t)
    if t[0] == 's':
        u, p = normalize_with_proof(t[1])
        return S(u), ['tr', S(1), p, refl(t)]
    _, n, a, h = t
    if n == 0:
        u, p = normalize_with_proof(a)
        return u, trans(['zero', a, h], p, t)
    if type(n) is list and n[0] == 's':
        r = k.sub(h, I(n[1], a, h))
        u, p = normalize_with_proof(r)
        return u, trans(['succ', n[1], a, h], p, t)
    return t, refl(t)


def computational_equality(a, b):
    na, pa = normalize_with_proof(a)
    nb, pb = normalize_with_proof(b)
    assert na == nb, (a, b, na, nb)
    return trans(pa, sym(pb, b), a)


def X(t):
    """D_(x,v) C(v,0,C(t,0,Sx)) = C(v,0,t)."""
    t = k.shift(t, 2)
    return ['d', eq(C(1, 0, C(t, 0, S(2))), C(1, 0, t))]


def X_at_zero(scope):
    matrix = X(0)[1]
    row = k.sub(k.sub(matrix, -scope, 2), S(-scope - 1))
    return ['di', matrix, computational_equality(row[1], row[2])]


def X_at_newest_successor(scope):
    assert scope > 0
    matrix = X(S(-scope))[1]
    row = k.sub(k.sub(matrix, -scope, 2), S(-scope - 1))
    return ['di', matrix, computational_equality(row[1], row[2])]


def coverage(t, scope, context_size=0):
    # Q_y X(y) is introduced through a D with its witness coordinate unused.
    # The inner X(Sz) is rebuilt after z has become the newest parameter.
    matrix = X(1)
    outer = ['di', matrix, X_at_newest_successor(scope + 1)]
    closure = ['de', outer, ['hyp', context_size]]
    return ['qe', t, closure, X_at_zero(scope)]


def certificate(scope, context, goal, proof):
    return dict(scope=scope, context=context, goal=goal, proof=proof)


def nodes(x):
    return 1 + sum(nodes(y) for y in x) if type(x) is list else 1


def main():
    examples = {}
    def add(name, scope, context, goal, proof):
        data = certificate(scope, context, goal, proof)
        k.check(data)
        examples[name] = data

    add('zero_computation', 0, [], eq(I(0, 0, 1), 0), ['zero', 0, 1])
    add('successor_computation', 1, [], eq(I(S(-1), 0, S(1)), S(I(-1, 0, S(1)))),
        ['succ', -1, 0, S(1)])
    add('reflexivity', 1, [], eq(-1, -1), refl(-1))
    add('hypothesis', 1, [eq(-1, 0)], eq(-1, 0), ['hyp', 0])
    add('symmetry', 1, [eq(-1, 0)], eq(0, -1), sym(['hyp', 0], -1))
    add('equation_progress', 0, [], ['q', eq(1, 1)],
        ['qi', eq(1, 1), refl(S(-1))])
    add('closure_use', 0, [], eq(S(0), S(0)),
        ['qe', S(0), ['qi', eq(1, 1), refl(S(-1))], refl(0)])
    add('closed_zero_witness', 0, [], ['d', eq(2, 0)], ['di', eq(2, 0), refl(0)])
    add('newest_witness', 1, [], ['d', eq(2, -1)], ['di', eq(2, -1), refl(-1)])
    for n in (0, 1, 2, 5):
        add(f'coverage_zero_scope_{n}', n, [], X(0), coverage(0, n))
        term = S(0) if n == 0 else I(S(-1), S(0), S(1))
        add(f'coverage_term_scope_{n}', n, [], X(term), coverage(term, n))
    # A fully checked generic successor naming packet with t an open parameter.
    t = -1
    add('symbolic_successor_packet', 1, [], X(S(t)), coverage(S(t), 1))
    # Check extraction of S(b)=S(t) in the opened packet context.  This is the
    # exact branch used before applying the separately proved predecessor.
    body = k.sub(X(S(t))[1], -2, 2)
    context = [['q', body]]
    base = k.sub(body, 0)
    row = k.sub(body, S(0))
    row_proof = ['qe', S(0), ['hyp', 0], computational_equality(base[1], base[2])]
    nl, pl = normalize_with_proof(row[1])
    nr, pr = normalize_with_proof(row[2])
    extracted = trans(sym(pl, row[1]), trans(row_proof, pr, row[1]), nl)
    assert nl == S(-2) and nr == S(-1)
    add('symbolic_successor_alias_branch', 2, context, eq(S(-2), S(-1)), extracted)

    rejected = {}
    def reject(name, data):
        try:
            k.check(data)
        except Exception:
            rejected[name] = True
        else:
            raise AssertionError('unsound certificate accepted: ' + name)
    reject('false_equation', certificate(0, [], eq(0, S(0)), refl(0)))
    reject('free_parameter_escape', certificate(0, [], eq(-1, -1), refl(-1)))
    reject('bound_index_escape', certificate(0, [], eq(1, 1), refl(1)))
    reject('boolean_as_number', certificate(0, [], eq(False, False), refl(False)))
    reject('compound_progress', certificate(0, [], ['q', ['d', eq(0, 0)]],
        ['qi', ['d', eq(0, 0)], ['di', eq(0, 0), refl(0)]]))
    reject('supplied_witness_field', certificate(0, [], ['d', eq(2, 0)],
        ['di', eq(2, 0), 0, refl(0)]))
    reject('old_witness_after_extension', certificate(1, [], ['d', eq(2, 0)],
        ['di', eq(2, 0), refl(0)]))
    reject('de_eigenparameter_escape', certificate(0, [], eq(0, 0),
        ['de', ['di', eq(0, 0), refl(0)], refl(-1)]))
    reject('wrong_hypothesis_index', certificate(0, [], eq(0, 0), ['hyp', 0]))
    reject('missing_closure_base', certificate(0, [], eq(S(0), S(0)),
        ['qe', S(0), ['qi', eq(1, 1), refl(S(-1))], refl(S(0))]))
    damaged = copy.deepcopy(examples['symbolic_successor_packet'])
    damaged['proof'][1] = 0
    reject('damaged_generic_packet', damaged)

    folder = ROOT / 'examples' / 'native'
    folder.mkdir(parents=True, exist_ok=True)
    for name, data in examples.items():
        (folder / (name + '.json')).write_text(json.dumps(data, separators=(',', ':')) + '\n')
    evidence = dict(status='PASS', accepted=len(examples), rejected=len(rejected),
        accepted_examples={name: dict(json_bytes=len(json.dumps(data, separators=(',', ':'))),
                                      tree_nodes=nodes(data['proof'])) for name, data in examples.items()},
        rejected_cases=list(rejected),
        scope='Finite native certificates, including a symbolic coverage packet and its alias branch; '
              'not a formal verification of completeness or the entire predecessor theorem.')
    (ROOT / 'evidence' / 'native_verification.json').write_text(json.dumps(evidence, indent=2) + '\n')
    print(json.dumps(evidence, indent=2))


if __name__ == '__main__':
    main()

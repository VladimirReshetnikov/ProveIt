"""Exercise constructive proof translations with the actual standalone kernels.

These finite tests check the implementation; the report's structural proof
establishes the general equivalence.  Run with Python 3.10 or later.
"""
import copy
import json
from pathlib import Path
import subprocess
import sys
import proof_translations as t

ROOT = Path(__file__).resolve().parent


def certificate(n, g, a, p):
    return dict(variables=n, context=g, goal=a, proof=p)


def iterate_equality(a, b, h=t.SV):
    return t.eq(['i', t.V, a, h], ['i', t.V, b, h])


def progress(e, a, b, h=t.SV, local=None):
    if local is None:
        middle = t.congr(h, t.hyp(e))
    else:
        middle = local
    return t.between(t.comp(t.V, a, h), middle, t.comp(t.V, b, h))


def accepted(kernel, c):
    try:
        kernel.check(c)
        return True
    except (ValueError, TypeError, IndexError, KeyError, RecursionError):
        return False


def replace_hyp(p, index, replacement):
    if p == ['hyp', index]:
        return copy.deepcopy(replacement)
    return [replace_hyp(x, index, replacement) if isinstance(x, list) else x for x in p]


def build_cases():
    cases = []
    cases.append(('successor_computation', certificate(0, [],
        t.comp(t.Z, t.Z, t.Z).a, t.comp(t.Z, t.Z, t.Z).p)))
    r = t.refl(t.Z)
    cases.append(('derived_reflexivity', certificate(0, [], r.a, r.p)))

    e = t.eq(['i', t.V, t.Z, t.SV], t.V)
    step = t.trans(t.comp(t.V, t.Z, t.SV), t.congr(t.SV, t.hyp(e)))
    cases.append(('identity_iterator_induction', certificate(0, [], ['q', e], ['qi', e, step.p])))

    a, b = ['v', 1], ['v', 2]
    e = iterate_equality(a, b)
    step = progress(e, a, b)
    cases.append(('nonreflexive_base_induction', certificate(2, [], ['q', e], ['qi', e, step.p])))

    h = ['i', t.V, t.Z, t.SV]
    e2 = iterate_equality(a, b, h)
    st2 = progress(e2, a, b, h)
    cases.append(('nested_update_induction', certificate(2, [], ['q', e2], ['qi', e2, st2.p])))

    # The source proof deliberately uses the retained context instead of IH.
    seed_template = ['i', ['s', ['v', 1]], t.V, t.SV]
    direct = t.congr(seed_template, t.hyp(t.eq(a, b), 1))
    cases.append(('induction_with_retained_hypothesis', certificate(2,
        [t.eq(['v', 0], ['v', 1])], ['q', e], ['qi', e, direct.p])))

    # A QI proof under a D-introduction eigenvariable and local hypothesis.
    inner_a, inner_b = ['v', 2], ['v', 3]
    inner_e = iterate_equality(inner_a, inner_b)
    inner_step = progress(inner_e, inner_a, inner_b)
    matrix = ['q', iterate_equality(['v', 3], ['v', 4])]
    nested = ['di', matrix, t.Z, ['qi', inner_e, inner_step.p]]
    cases.append(('induction_inside_case_binder', certificate(2, [], ['d', matrix], nested)))

    # Case DI whose reflexive base hypothesis is used in the proof tree.
    er = iterate_equality(t.Z, t.Z)
    used_base = t.congr(seed_template, t.hyp(t.eq(t.Z, t.Z)))
    cases.append(('reflexive_case_base_used', certificate(0, [], ['d', t.dummy(er)],
        ['di', t.dummy(er), t.Z, used_base.p])))

    # Literal-zero witness is a case rule when the base is nonreflexive.
    direct0 = t.congr(seed_template, t.hyp(t.eq(a, b)))
    cases.append(('zero_witness_nonreflexive_case', certificate(2, [], ['d', t.dummy(e)],
        ['di', t.dummy(e), t.Z, direct0.p])))
    return cases


def main():
    out = ROOT / 'examples'
    out.mkdir(exist_ok=True)
    records, process_runs = [], 0
    for name, source in build_cases():
        t.seven.check(source)
        forward = t.translate_certificate(source, 'to_six')
        backward = t.translate_certificate(forward, 'to_seven')
        assert source['goal'] == forward['goal'] == backward['goal']
        assert source['context'] == forward['context'] == backward['context']
        for suffix, c in [('seven', source), ('six', forward), ('roundtrip', backward)]:
            (out / f'{name}_{suffix}.json').write_text(json.dumps(c, indent=2) + '\n')
        records.append(dict(name=name, forward=True, backward=True,
                            source_json_bytes=len(json.dumps(source)),
                            target_json_bytes=len(json.dumps(forward))))
        for optimized in (False, True):
            for module, c in [('zero_seven.py', source), ('reflexive_base.py', forward),
                              ('zero_seven.py', backward)]:
                args = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT / module)]
                run = subprocess.run(args, input=json.dumps(c), text=True, capture_output=True)
                assert run.returncode == 0 and run.stdout.strip() == 'ACCEPT', (name, args, run.stderr)
                process_runs += 1

    # Nonzero witness: mode is selected by the base, never by the witness.
    e = iterate_equality(t.Z, t.Z)
    step = progress(e, t.Z, t.Z)
    guarded = certificate(0, [], ['d', t.dummy(e)],
                          ['di', t.dummy(e), ['s', t.Z], step.p])
    t.six.check(guarded)
    t.translate_certificate(guarded, 'to_seven')
    (out / 'nonzero_witness_progress_six.json').write_text(json.dumps(guarded, indent=2) + '\n')
    records.append(dict(name='nonzero_witness_progress', backward=True))

    # A substitution makes two unequal base terms literally identical.
    a, b = ['v', 1], ['v', 2]
    e = iterate_equality(a, b)
    template = ['i', ['s', ['v', 1]], t.V, t.SV]
    step = t.congr(template, t.hyp(t.eq(a, b)))
    original = certificate(2, [], ['d', t.dummy(e)],
                           ['di', t.dummy(e), ['s', t.Z], step.p])
    t.six.check(original)
    changed = t.substitute_guarded_certificate(original, [t.Z, t.Z], 0)
    naive = dict(changed, proof=t.substitute_seven_tree(original['proof'], [t.Z, t.Z]))
    assert not accepted(t.six, naive)
    for name, c in [('guard_change_before', original), ('guard_change_after', changed),
                    ('guard_change_naive_rejected', naive)]:
        (out / f'{name}.json').write_text(json.dumps(c, indent=2) + '\n')
    records.append(dict(name='false_to_true_guard_substitution', elaborated=True, naive_rejected=True))

    # A zero-normalization contraction, rather than variable identification,
    # changes the guard: I(x,0;u.0)=0 becomes 0=0 when x is replaced by zero.
    initializer = ['i', ['v', 1], t.Z, t.Z]
    e = iterate_equality(initializer, t.Z)
    step = t.congr(template, t.hyp(t.eq(initializer, t.Z)))
    before = certificate(1, [], ['d', t.dummy(e)], ['di', t.dummy(e), t.Z, step.p])
    t.six.check(before)
    after = t.substitute_guarded_certificate(before, [t.Z], 0)
    naive = dict(after, proof=t.substitute_seven_tree(before['proof'], [t.Z]))
    assert not accepted(t.six, naive)
    (out / 'normalization_guard_change_before.json').write_text(json.dumps(before, indent=2) + '\n')
    (out / 'normalization_guard_change_after.json').write_text(json.dumps(after, indent=2) + '\n')
    records.append(dict(name='normalization_changes_guard', elaborated=True, naive_rejected=True))

    # Check that the nonreflexive progress premise is actually indispensable
    # to the given source certificate, rather than merely an ignored packet.
    source = dict(build_cases()[3][1])
    lhs = source['goal'][1][1]
    source['proof'] = replace_hyp(source['proof'], 0, t.refl(lhs).p)
    assert not accepted(t.seven, source)
    records.append(dict(name='induction_hypothesis_mutation', rejected=True))

    good = t.translate_certificate(build_cases()[3][1], 'to_six')
    invalid = []
    def mutate(name, f):
        c = copy.deepcopy(good)
        f(c)
        invalid.append((name, c))
    mutate('boolean_scope', lambda c: c.update(variables=True))
    mutate('negative_scope', lambda c: c.update(variables=-1))
    mutate('float_scope', lambda c: c.update(variables=2.0))
    mutate('extra_envelope_key', lambda c: c.update(extra=0))
    mutate('missing_goal', lambda c: c.pop('goal'))
    mutate('boolean_term_index', lambda c: c.update(goal=t.eq(['v', True], t.Z)))
    mutate('negative_term_index', lambda c: c.update(goal=t.eq(['v', -1], t.Z)))
    mutate('out_of_scope_term', lambda c: c.update(goal=t.eq(['v', 2], t.Z)))
    mutate('zero_counter_not_normal', lambda c: c.update(goal=t.eq(['i', t.Z, t.Z, t.Z], t.Z)))
    mutate('unknown_term_tag', lambda c: c.update(goal=t.eq(['unknown'], t.Z)))
    mutate('unknown_formula_tag', lambda c: c.update(goal=['unknown', t.Z]))
    mutate('unknown_proof_tag', lambda c: c.update(proof=['qi', t.eq(t.Z, t.Z), ['hyp', 0]]))
    mutate('negative_hypothesis', lambda c: c.update(proof=['hyp', -1]))
    mutate('boolean_hypothesis', lambda c: c.update(proof=['hyp', True]))
    mutate('eigenvariable_escape', lambda c: c.update(proof=['de', t.eq(['v', 2], t.Z), ['hyp', 0], ['hyp', 0]]))
    mutate('malformed_context', lambda c: c.update(context=[['=', ['v', 99], t.Z]]))
    for name, c in invalid:
        assert not accepted(t.six, c), name
        for optimized in (False, True):
            args = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT / 'reflexive_base.py')]
            run = subprocess.run(args, input=json.dumps(c), text=True, capture_output=True)
            assert run.returncode != 0 and run.stdout.strip() != 'ACCEPT', name
            process_runs += 1

    report = dict(python=sys.version, translation_cases=records,
                  rejection_cases=[name for name, _ in invalid],
                  standalone_process_checks=process_runs,
                  all_passed=True,
                  qualification='Finite execution tests, not a proof-assistant verification.')
    (ROOT / 'translation_verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(dict(all_passed=True, translation_cases=len(records),
                          rejection_cases=len(invalid), standalone_process_checks=process_runs)))


if __name__ == '__main__':
    main()

"""Reproduce matched measurements, proof translations, and finite checks.

These executable checks are evidence about the implementation. They are not
a proof of the universal calculus-equivalence or bi-interpretation theorems.
"""

import ast
import copy
import gzip
import hashlib
import io
import json
from pathlib import Path
import random
import subprocess
import sys
import tokenize

import checker as single
import normalized_control as normal
import raw_control as raw
import raw_two_case as two
from translate import root_compose, translate


HERE = Path(__file__).resolve().parent
Z = ['z']
ONE = ['s', Z]
V = lambda i: ['v', i]
S = lambda a: ['s', a]
I = lambda c, a, h: ['i', c, a, h]
E = lambda a, b: ['=', a, b]
R = lambda a: ['refl', a]
EV = lambda p, q: ['ev', p, q]


def canonical(a):
    """Independent zero-normalizer used only by the test harness."""
    if a[0] in ('v', 'z'):
        return copy.deepcopy(a)
    if a[0] == 's':
        return S(canonical(a[1]))
    if a[0] == 'i':
        counter, seed, update = [canonical(b) for b in a[1:]]
        return seed if counter == Z else I(counter, seed, update)
    if a[0] == '=':
        return E(canonical(a[1]), canonical(a[2]))
    return [a[0], canonical(a[1])]


def certificate(module, proof, context=(), variables=0):
    goal = module.infer(proof, list(context), variables)
    result = {'variables': variables, 'context': list(context),
              'goal': goal, 'proof': proof}
    module.check(result)
    return result


def congruence(p, s, h, normalized=False):
    """From p:s=t derive h(s)=h(t) using only the restricted Eval."""
    whole = I(ONE, s, h)
    if normalized:
        left = EV(p, R(whole))
        right = EV(R(s), R(whole))
    else:
        predecessor = I(Z, s, h)
        left = EV(EV(p, R(predecessor)), R(whole))
        right = EV(EV(R(s), R(predecessor)), R(whole))
    return root_compose(left, right, whole, normalized)


def positive_cases(normalized=False):
    module = normal if normalized else raw
    selected = single if normalized else two
    cases = {}
    cases['reflexivity_zero'] = certificate(module, R(Z))
    cases['reflexivity_open_variable'] = certificate(module, R(V(0)), variables=1)
    cases['root_bootstrap_open'] = certificate(
        module, EV(['hyp', 0], ['hyp', 1]), [E(V(0), V(1)), E(V(0), V(2))], 3)
    bridge = I(ONE, V(0), V(0)) if normalized else I(Z, V(0), Z)
    cases['root_bootstrap_expanded'] = certificate(
        selected, root_compose(['hyp', 0], ['hyp', 1], V(0), normalized),
        [E(V(0), V(1)), E(V(0), V(2))], 3)
    cases['bootstrap_bridge'] = certificate(
        selected, EV(['hyp', 0], R(bridge)), [E(V(0), V(1))], 2)
    cases['symmetry_open'] = certificate(
        selected, root_compose(R(V(0)), ['hyp', 0], V(0), normalized),
        [E(V(0), V(1))], 2)
    swapped = root_compose(R(V(0)), ['hyp', 0], V(0), normalized)
    cases['transitivity_open'] = certificate(
        selected, root_compose(['hyp', 1], swapped, V(1), normalized),
        [E(V(0), V(1)), E(V(1), V(2))], 3)

    # Nontrivial templates include several occurrences, parameters, and binders.
    templates = [V(0), S(V(0)), I(V(0), V(1), S(V(0))),
                 I(V(1), V(0), I(V(1), V(2), S(V(0)))),
                 I(S(V(0)), I(V(0), V(1), V(0)), S(V(2)))]
    for j, h in enumerate(templates):
        h = canonical(h) if normalized else h
        p = congruence(['hyp', 0], V(0), h, normalized)
        c = certificate(selected, p, [E(V(0), V(1))], 2)
        assert c['goal'] == E(selected.sub(h, V(0)), selected.sub(h, V(1)))
        cases['congruence_' + str(j)] = c
        q = ['hyp', 1]
        crossed = root_compose(p, q, selected.sub(h, V(0)), normalized)
        cases['crossed_transport_' + str(j)] = certificate(
            selected, crossed, [E(V(0), V(1)), E(selected.sub(h, V(0)), V(0))], 2)

    # The induction step uses the induction hypothesis as its Eval major.
    update = S(V(0))
    matrix = E(I(V(0), Z, update), V(0))
    step = EV(['hyp', 0], R(I(S(V(0)), Z, update)))
    induction = ['di', matrix, Z, step]
    cases['used_induction_hypothesis'] = certificate(selected, induction)

    # DE and QE recover an explicit numerical consequence of that induction.
    base = R(Z) if normalized else EV(R(Z), R(I(Z, Z, update)))
    result = E(I(ONE, Z, update), ONE)
    qe = ['qe', ONE, ['hyp', 0], base]
    cases['induction_de_qe'] = certificate(
        selected, ['de', result, induction, qe])
    cases['compound_case_introduction'] = certificate(
        selected, ['di', ['d', E(Z, Z)], Z, ['hyp', 0]])
    cases['literal_case_nonzero_witness'] = certificate(
        selected, ['di', E(V(1), V(1)), ONE, ['hyp', 0]])
    zero_alias = I(ONE, Z, Z)
    cases['literal_case_computable_zero_witness'] = certificate(
        selected, ['di', E(V(1), V(1)), zero_alias, ['hyp', 0]])

    if normalized:
        # Substitution exposes a zero counter in the update and contracts it.
        h = I(V(0), ONE, S(V(0)))
        cases['substitution_exposes_zero'] = certificate(
            selected, EV(R(Z), R(I(ONE, Z, h))))
        cases['zero_alias_equation'] = certificate(
            selected, EV(R(Z), R(zero_alias)))
    else:
        cases['zero_computation'] = certificate(
            selected, EV(R(V(0)), R(I(Z, V(0), S(V(0))))), variables=1)
        cases['successor_computation'] = certificate(
            selected, EV(R(I(V(0), Z, update)), R(I(S(V(0)), Z, update))), variables=1)
    return cases


def negative_cases():
    good = {'variables': 0, 'context': [], 'goal': E(Z, Z), 'proof': R(Z)}
    cases = {}

    def change(name, **kwargs):
        c = copy.deepcopy(good)
        c.update(kwargs)
        cases[name] = c

    change('unproved_contradiction', goal=E(Z, ONE))
    change('negative_variable_count', variables=-1)
    change('boolean_variable_count', variables=False)
    change('float_variable_count', variables=0.0)
    change('extra_top_level_field', extra=0)
    change('invalid_context_type', context={})
    change('out_of_scope_goal', goal=E(V(0), V(0)))
    change('out_of_scope_reflexivity', proof=R(V(0)))
    change('negative_hypothesis', proof=['hyp', -1])
    change('boolean_hypothesis', proof=['hyp', False])
    change('float_hypothesis', proof=['hyp', 0.0])
    change('unknown_rule', proof=['magic', Z])
    change('extra_rule_argument', proof=['refl', Z, Z])
    change('malformed_successor', proof=R(['s']))
    change('boolean_variable', variables=1, proof=R(['v', False]))
    change('float_variable', variables=1, proof=R(['v', 0.0]))
    change('negative_variable', variables=1, proof=R(V(-1)))
    change('invalid_constructor', proof=R(['zero']))
    change('mismatched_eval_source', proof=EV(R(ONE), R(I(ONE, Z, V(0)))))
    change('non_successor_counter', variables=1,
           proof=EV(R(Z), R(I(V(0), Z, V(0)))))
    change('qe_wrong_major', proof=['qe', Z, R(Z), R(Z)])
    change('de_wrong_major', proof=['de', E(Z, Z), R(Z), R(Z)])
    change('di_witness_capture', proof=['di', E(V(0), V(0)), V(0), R(V(0))])
    change('de_conclusion_capture', proof=['de', E(V(0), V(0)), R(Z), R(V(0))])
    change('wrong_progress_conclusion', proof=['di', E(V(0), V(0)), Z, ['hyp', 0]])
    return cases


def proof_nodes(p):
    if p[0] in ('hyp', 'refl'):
        return 1
    if p[0] == 'ev':
        return 1 + proof_nodes(p[1]) + proof_nodes(p[2])
    if p[0] in ('qe', 'de'):
        return 1 + proof_nodes(p[2]) + proof_nodes(p[3])
    return 1 + proof_nodes(p[3])


def metrics(path):
    text = ast.unparse(ast.parse(path.read_text())) + '\n'
    data = text.encode()
    excluded = {tokenize.ENCODING, tokenize.NL, tokenize.NEWLINE,
                tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER, tokenize.COMMENT}
    tokens = [t for t in tokenize.generate_tokens(io.StringIO(text).readline)
              if t.type not in excluded]
    path.with_name(path.stem + '.normalized.py').write_bytes(data)
    compressed = gzip.compress(data, compresslevel=9, mtime=0)
    path.with_name(path.stem + '.normalized.py.gz').write_bytes(compressed)
    return {'tokens': len(tokens), 'ast_nodes': sum(1 for _ in ast.walk(ast.parse(text))),
            'normalized_bytes': len(data), 'gzip9_bytes': len(compressed),
            'sha256_normalized': hashlib.sha256(data).hexdigest()}


def process_check(path, value, expected, optimized=False):
    cmd = [sys.executable] + (['-O'] if optimized else []) + [str(path)]
    completed = subprocess.run(cmd, input=json.dumps(value), capture_output=True, text=True)
    accepted = completed.returncode == 0 and completed.stdout == 'ACCEPT\n'
    assert accepted == expected, (str(path), expected, completed.returncode,
                                 completed.stdout, completed.stderr, value)


def random_term(rng, variables, depth):
    if depth == 0:
        return Z if rng.randrange(3) == 0 else V(rng.randrange(variables))
    tag = rng.randrange(4)
    if tag == 0:
        return random_term(rng, variables, 0)
    if tag == 1:
        return S(random_term(rng, variables, depth - 1))
    if tag == 2:
        # Small counters control the independent evaluator's running time.
        count = [Z, ONE, S(ONE), V(rng.randrange(variables))][rng.randrange(4)]
        return I(count, random_term(rng, variables, depth - 1),
                 random_term(rng, variables + 1, depth - 1))
    return I(Z, random_term(rng, variables, depth - 1),
             random_term(rng, variables + 1, depth - 1))


def evaluate(a, environment, fuel):
    fuel[0] -= 1
    if fuel[0] < 0:
        raise OverflowError('Test evaluation budget')
    tag = a[0]
    if tag == 'v':
        return environment[a[1]]
    if tag == 'z':
        return 0
    if tag == 's':
        return 1 + evaluate(a[1], environment, fuel)
    counter = evaluate(a[1], environment, fuel)
    state = evaluate(a[2], environment, fuel)
    for _ in range(counter):
        state = evaluate(a[3], [state] + environment, fuel)
    return state


def normalization_checks():
    rng = random.Random(361194)
    evaluated = 0
    structural = 0
    attempts = 0
    while evaluated < 320:
        attempts += 1
        body = random_term(rng, 3, 3)
        image = random_term(rng, 2, 2)
        raw.term(body, 3)
        raw.term(image, 2)
        nb, ni = canonical(body), canonical(image)
        single.term(nb, 3)
        single.term(ni, 2)
        assert canonical(nb) == nb
        assert canonical(raw.shift(body, 2)) == single.shift(nb, 2)
        assert canonical(raw.sub(body, image)) == single.sub(nb, ni)
        # Additional enclosing Q/D binders exercise capture-avoiding traversal.
        formula = ['d', ['q', E(raw.shift(body, 3), V(0))]]
        raw.formula(formula, 3)
        assert canonical(raw.sub(formula, image)) == single.sub(canonical(formula), ni)
        structural += 4
        values = [rng.randrange(3), rng.randrange(3)]
        try:
            replacement = evaluate(image, values, [50000])
            ordinary = evaluate(body, [replacement] + values, [50000])
            result = evaluate(single.sub(nb, ni), values, [50000])
            normalized = evaluate(nb, [replacement] + values, [50000])
        except OverflowError:
            continue
        assert ordinary == result == normalized
        evaluated += 1
    return {'structural_commutation_checks': structural,
            'independent_numerical_substitution_checks': evaluated,
            'generated_attempts': attempts}


def main():
    result = {'python': sys.version, 'metrics': {}, 'families': {}}
    for name in ('raw_control.py', 'raw_two_case.py', 'normalized_control.py', 'checker.py'):
        result['metrics'][name] = metrics(HERE / name)
    blob = (HERE / 'raw_control.py').read_bytes()
    sha = hashlib.sha1(b'blob ' + str(len(blob)).encode() + b'\0' + blob).hexdigest()
    assert sha == 'fb0c113d07d3d25632e8c077f91268f089f71bf3'
    result['upstream_control_git_blob_sha1'] = sha
    total_processes = 0
    for normalized in (False, True):
        family = 'normalized' if normalized else 'raw'
        source, target = (normal, single) if normalized else (raw, two)
        target_name = 'checker.py' if normalized else 'raw_two_case.py'
        cases = positive_cases(normalized)
        if not normalized:
            for path in (HERE / 'upstream_examples').glob('*.json'):
                cases['upstream_' + path.stem] = json.loads(path.read_text())
        output = HERE / 'certificates' / family
        output.mkdir(parents=True, exist_ok=True)
        node_bounds = []
        for name, c in cases.items():
            source.check(c)
            d = translate(c, normalized)
            assert (c['variables'], c['context'], c['goal']) == (
                d['variables'], d['context'], d['goal'])
            target.check(d)
            source.check(d)  # Reverse translation is the identity proof tree.
            before, after = proof_nodes(c['proof']), proof_nodes(d['proof'])
            assert after <= 3 * before
            node_bounds.append({'name': name, 'before': before, 'after': after})
            (output / (name + '.json')).write_text(json.dumps(d, indent=2) + '\n')
            for filename in (target_name, target_name.replace('.py', '.normalized.py')):
                for optimized in (False, True):
                    process_check(HERE / filename, d, True, optimized)
                    total_processes += 1
        negative = negative_cases()
        if normalized:
            negative['noncanonical_iterator'] = {
                'variables': 0, 'context': [], 'goal': E(Z, Z), 'proof': R(I(Z, Z, Z))}
            negative['noncanonical_binder_body'] = {
                'variables': 0, 'context': [], 'goal': E(Z, Z),
                'proof': R(I(ONE, Z, I(Z, V(0), Z)))}
        for name, c in negative.items():
            for filename in (target_name, target_name.replace('.py', '.normalized.py')):
                for optimized in (False, True):
                    process_check(HERE / filename, c, False, optimized)
                    total_processes += 1
        # The source's bare root step is intentionally absent in the target.
        eliminated = {'variables': 0, 'context': [], 'goal': E(Z, Z),
                      'proof': EV(R(Z), R(Z))}
        source.check(eliminated)
        process_check(HERE / target_name, eliminated, False)
        process_check(HERE / target_name, translate(eliminated, normalized), True)
        total_processes += 2
        result['families'][family] = {'positive_cases': len(cases),
                                     'negative_cases': len(negative),
                                     'round_trips': len(cases),
                                     'proof_node_bound_checks': node_bounds}
    result['normalization'] = normalization_checks()
    result['standalone_process_checks'] = total_processes
    result['unexpected_outcomes'] = 0
    result['limitations'] = [
        'Finite executable checks do not establish universal metatheorems.',
        'No Lean or Rocq verification of the Python modules is claimed.',
        'The two proof compilers compare fixed interfaces; neither is a raw-to-canonical compiler.',
        'Compressed-codec global minima use a different input and validation contract.'
    ]
    (HERE / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'families'}, indent=2))
    print('All checks passed.')


if __name__ == '__main__':
    main()

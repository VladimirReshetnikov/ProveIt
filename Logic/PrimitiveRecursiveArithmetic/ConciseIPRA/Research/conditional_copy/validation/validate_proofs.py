"""Build and replay certificates for the new deterministic calculus.

This is an untrusted proof producer and regression audit. It is not imported
by the acceptance checker, and finite tests do not replace the written proof.
"""
from pathlib import Path
import copy
import json
import subprocess
import sys

HERE = Path(__file__).resolve().parent
CODE = HERE.parent / 'code'
EVIDENCE = HERE.parent / 'evidence'
sys.path.insert(0, str(CODE))

import checker
import proof_tools as p
import translate_witness


def build_examples():
    examples = {}

    def add(name, proof, description):
        goal = checker.prove(proof, p.INITIAL)
        examples[name] = ([goal, proof], description)

    add('reflexivity', p.refl(p.ONE), 'Use of the fixed reflexivity clause.')
    for depth in range(4):
        H = [p.V, p.ONE]
        for _ in range(depth):
            H = p.D(p.gate(p.Y, H))
        for k, s in enumerate([0, p.ONE, p.TWO]):
            add(f'delta_depth{depth}_numeral{k}', p.delta_proof(s, H),
                'Equality-free witness-transfer theorem at arbitrary formula depth.')
    for k, t in enumerate([p.ONE, p.TWO]):
        for depth in range(3):
            A = [p.X, t]
            for _ in range(depth):
                A = p.D(p.gate(p.Y, A), p.U, p.Y)
            goal = p.D(p.gate(p.Y, A))
            add(f'arbitrary_intro_depth{depth}_witness{k+1}',
                p.arbitrary_intro(goal[0], t, p.reflexive_tower),
                'Derived introduction at a numeral different from the selected root witness.')
    induction = p.D([p.identity_iterator(p.Y), 0])
    add('arbitrary_intro_used_progress',
        p.arbitrary_intro(induction[0], p.TWO,
                          lambda local, goal: p.use(len(local) - 1)),
        'Derived introduction preserves an actually used atomic progress hypothesis.')
    A, B = -200001, -200002
    F = p.implication_formula([A, B], [p.S(B), p.S(A)])

    def outer_builder(g, a):
        inner_template = p.at(F, A, a)

        def inner_builder(local, b):
            return p.implication([a, b], [p.S(b), p.S(a)],
                lambda ext, hyp: p.transport(hyp, lambda _: p.refl(p.S(a)),
                                             p.S(p.V), p.V, ext), local)

        return p.all_intro(inner_template, B, inner_builder, g)

    add('universal_successor_congruence',
        p.all_intro(p.all_formula(F, B), A, outer_builder),
        'For all a,b: a=b implies S(b)=S(a), through a nontrivial inferred Export.')
    naming = p.D(p.gate(p.Y, [p.X, p.TWO]))
    major = p.arbitrary_intro(naming[0], p.TWO, p.reflexive_tower)
    add('inferred_export_reflexivity', [[], major, p.refl(-1)],
        'Export recognizes b=2 and substitutes 2 for the fresh b.')
    nested_goal = p.D([-1, -1])
    opened_body = p.sub(naming[0], -1, 1)
    local = p.INITIAL + [(p.sub(opened_body, 0), opened_body)]
    nested = p.reflexive_tower(local, nested_goal)
    add('inferred_export_under_binder', [[], major, nested],
        'The inferred replacement passes capture-avoidably through a D binder.')

    def self_target_builder(g, hypothesis):
        packet = p.D(p.gate(p.Y, [p.X, p.S(p.X)]))
        maj = p.arbitrary_intro(packet[0], 0,
                               lambda ext, goal: hypothesis(ext), g)
        return [[], maj, p.refl(0)]

    add('self_containing_replacement_unused',
        p.implication([0, p.ONE], [0, 0], self_target_builder),
        'A selected replacement containing b is allowed when the exported formula ignores b.')
    return examples


def rejected_examples(positive):
    truth_d = [[0, 0]]
    dummy = [truth_d[0], p.refl(0)]
    naming = p.D(p.gate(p.Y, [p.X, p.ONE]))
    naming_major = p.arbitrary_intro(naming[0], p.ONE, p.reflexive_tower)
    nonzero_base = p.D([[p.Y, 0, 1], p.ONE])
    base_not_truth = p.D([p.X, p.ONE])
    base_not_truth_major = p.arbitrary_intro(base_not_truth[0], p.ONE, p.reflexive_tower)
    row_not_variable = p.D(p.gate(p.Y, [p.S(p.X), p.S(p.ONE)]))
    row_not_variable_major = p.arbitrary_intro(row_not_variable[0], p.ONE,
                                              p.reflexive_tower)
    return {
        'false_equation': [[0, p.ONE], p.refl(0)],
        'boolean_goal_alias': [[False, False], p.refl(0)],
        'float_goal_alias': [[0.0, 0.0], p.refl(0)],
        'negative_clause_index': [[0, 0], [-1, 0, None]],
        'boolean_opcode': [[0, 0], [False, 0, None]],
        'out_of_scope_use_term': [[-1, -1], p.refl(-1)],
        'extra_introduction_witness': [truth_d, [truth_d[0], p.ONE, p.refl(0)]],
        'extra_export_equality': [[0, 0], [[], dummy, p.refl(-1), p.refl(0)]],
        'fallback_fresh_escape': [[0, 0], [[], dummy, p.refl(-1)]],
        'nontruth_base_cannot_name': [[p.ONE, p.ONE],
                                    [[], base_not_truth_major, p.refl(-1)]],
        'nonvariable_first_row_cannot_name': [[p.ONE, p.ONE],
                                    [[], row_not_variable_major, p.refl(-1)]],
        'nonzero_reflexivity_cannot_select_progress':
            [nonzero_base, [nonzero_base[0], p.use(1)]],
        'forged_inferred_replacement': [[p.TWO, p.TWO],
                                      [[], naming_major, p.refl(-1)]],
        'wrong_clause_antecedent': [[0, 0],
                                  [[], naming_major, p.use(1, p.ONE, p.refl(p.ONE))]],
        'erased_boolean_body': [[p.ONE, p.ONE], [0, [0, 0, False], None]],
        'erased_ill_scoped_body': [[p.ONE, p.ONE], [0, [0, 0, 99], None]],
    }


def cli(payload, optimized):
    command = [sys.executable, '-I', '-S', '-B']
    if optimized:
        command.append('-O')
    result = subprocess.run(command + [str(CODE / 'checker.py')],
                            input=json.dumps(payload).encode(),
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            timeout=20)
    return result.returncode == 0 and result.stdout == b'ACCEPT\n'


def main():
    positive = build_examples()
    negative = rejected_examples(positive)
    records = []
    for directory, examples, expected in [('positive', positive, True),
                                          ('negative', negative, False)]:
        target = HERE / 'fixtures' / directory
        target.mkdir(parents=True, exist_ok=True)
        for name, record in examples.items():
            payload, description = record if expected else (record, name.replace('_', ' '))
            try:
                checker.check(copy.deepcopy(payload))
                actual = True
            except Exception:
                actual = False
            if actual != expected:
                raise AssertionError((name, expected, actual))
            for optimized in (False, True):
                if cli(payload, optimized) != expected:
                    raise AssertionError((name, 'CLI', optimized))
            path = target / (name + '.json')
            path.write_text(json.dumps(payload, separators=(',', ':')) + '\n')
            records.append({'file': str(path.relative_to(HERE)),
                            'accepted': actual, 'description': description})
    open_checks = 0
    for depth in range(3):
        H = [p.S(p.V), p.S(p.V)]
        for _ in range(depth):
            H = p.D(p.gate(p.Y, H))
        g = p.INITIAL + [([], [0, 0])]
        s = [-1, 0, 2]
        q = p.delta_proof(s, H, g)
        if checker.prove(q, g) != p.delta(s, H):
            raise AssertionError(('open scope', depth))
        open_checks += 1
    translations = 0
    translation_records = []

    def proof_nodes(proof):
        code, *args = proof
        if type(code) is int:
            return 1 + (proof_nodes(args[1]) if args[1] is not None else 0)
        if code:
            return 1 + proof_nodes(args[-1])
        return 1 + proof_nodes(args[0]) + proof_nodes(args[1])

    def record_translation(name, old, new, open_scope=False):
        translation_records.append({
            'name': name, 'open_scope': open_scope,
            'source_proof_nodes': proof_nodes(old),
            'target_proof_nodes': proof_nodes(new),
            'source_proof_json_bytes': len(json.dumps(old, separators=(',', ':')).encode()),
            'target_proof_json_bytes': len(json.dumps(new, separators=(',', ':')).encode()),
        })
    source_directory = HERE / 'fixtures' / 'source'
    translated_directory = HERE / 'fixtures' / 'translated'
    source_directory.mkdir(exist_ok=True)
    translated_directory.mkdir(exist_ok=True)
    for k, term in enumerate([p.ONE, p.TWO], 1):
        goal = p.D(p.gate(p.Y, [p.X, term]))
        old = [goal[0], term, p.refl(term)]
        translate_witness.source.check([goal, old])
        new = translate_witness.translate(old)
        checker.check([goal, new])
        file = f'explicit_witness{k}.json'
        (source_directory / file).write_text(json.dumps([goal, old], separators=(',', ':')) + '\n')
        (translated_directory / file).write_text(json.dumps([goal, new], separators=(',', ':')) + '\n')
        record_translation(file[:-5], old, new)
        translations += 1
    for name in ['delta_depth1_numeral1', 'arbitrary_intro_used_progress',
                 'universal_successor_congruence']:
        payload, _ = positive[name]
        goal, proof = payload
        old = translate_witness.forget_determinism(proof)
        translate_witness.source.check([goal, old])
        translated = [goal, translate_witness.translate(old)]
        checker.check(translated)
        (source_directory / (name + '.json')).write_text(
            json.dumps([goal, old], separators=(',', ':')) + '\n')
        (translated_directory / (name + '.json')).write_text(
            json.dumps(translated, separators=(',', ':')) + '\n')
        record_translation(name, old, translated[1])
        translations += 1
    old_context = p.INITIAL + [([], [0, 0])]
    new_context = p.INITIAL + [([], [0, 0]), ([], [0, 0])]
    naming = p.D(p.gate(p.Y, [p.X, -1]))
    old = [[], [naming[0], -1, p.refl(-1)], p.refl(-2)]
    changed_scope = translate_witness.translate(old, old_context, new_context,
                                               {-1: -2}, [0, 2])
    if checker.prove(changed_scope, new_context) != [-2, -2]:
        raise AssertionError('nontrivial numerical/context embedding')
    record_translation('nontrivial_scope_embedding', old, changed_scope, True)
    translations += 1
    source_payload = json.loads((source_directory / 'explicit_witness2.json').read_text())
    cli_translation = subprocess.run(
        [sys.executable, '-B', str(CODE / 'translate_witness.py')],
        input=json.dumps(source_payload).encode(), stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, timeout=20)
    if cli_translation.returncode != 0:
        raise AssertionError(cli_translation.stderr.decode())
    checker.check(json.loads(cli_translation.stdout))
    result = {'accepted': len(positive), 'rejected': len(negative),
              'cli_runs': 2 * (len(positive) + len(negative)),
              'open_scope_checks': open_checks,
              'source_to_target_translations': translations,
              'translation_cli_runs': 1,
              'translations': translation_records,
              'records': records,
              'limitation': 'Finite implementation evidence; not a proof-assistant verification.'}
    EVIDENCE.mkdir(exist_ok=True)
    (EVIDENCE / 'proof_validation.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('records', 'translations')}, indent=2))


if __name__ == '__main__':
    main()

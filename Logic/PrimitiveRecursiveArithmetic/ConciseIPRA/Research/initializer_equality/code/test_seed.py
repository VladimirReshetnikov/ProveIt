"""Generate proofs and measure/test the complete strict checkers.

This is untrusted producer and regression code; it is not a proof assistant.
"""
import ast
import gzip
import hashlib
import io
import itertools
import json
from pathlib import Path
import subprocess
import sys
import tokenize

from translate import Builder, general, seed, to_general, to_seed

ROOT = Path(__file__).resolve().parent
S, I = general.successor, general.rec


def eq(a, b):
    return ['=', a, b]


def packet(goal, proof):
    return {'goal': goal, 'proof': proof}


def fixture_general():
    b = Builder('general')
    result = {}

    def add(name, proof, goal=None):
        actual = b.conclusion(proof)
        if goal is not None and actual != goal:
            raise RuntimeError((name, actual, goal))
        result[name] = packet(actual, proof)

    computation = ['r', 0, 0, 1]
    retract_zero = I(S(0), 0, 1)
    add('successor_computation', computation, eq(retract_zero, 0))
    add('reflexivity_zero', b.refl(0), eq(0, 0))
    add('reflexivity_successor', b.refl(S(0)), eq(S(0), S(0)))
    nested = I(S(S(0)), S(0), I(1, 0, S(1)))
    add('reflexivity_nested_iterator', b.refl(nested), eq(nested, nested))
    add('zero_source_root', b.sym(computation), eq(0, retract_zero))
    for name, template in [
        ('successor', S(1)),
        ('constant_zero', 0),
        ('zero_counter_exposed', I(1, 0, S(1))),
        ('nested_zero_counter_exposed', I(I(1, 0, 1), S(1), S(1))),
        ('repeated_hole', I(S(1), 1, S(2))),
        ('hole_under_state_binder', I(S(0), 0, S(2))),
        ('nested_state_binders', I(S(0), 1, I(S(1), 2, S(3))))]:
        add('congruence_' + name, b.congr(template, computation))
        add('zero_source_' + name, b.congr(template, b.sym(computation)))

    d = ['D', eq(1, 1)]
    branch = Builder('general', [eq(1, 1)], 1).refl(S(1))
    di = ['i', d, 0, branch]
    add('progress_introduction', di, d)
    q = ['Q', eq(1, 1)]
    qe_major = ['e', q, di, ['h', 0]]
    add('existential_to_closure', qe_major, q)
    add('ordinary_Q_elimination', ['q', nested, qe_major, b.refl(0)], eq(nested, nested))

    # A nontrivial, actually used equation-induction hypothesis.
    induction = ['D', eq(I(1, 0, S(1)), 1)]
    hyp = eq(I(1, 0, S(1)), 1)
    ib = Builder('general', [hyp], 1)
    step = ib.trans(['r', 1, 0, S(1)], ib.congr(S(1), ['h', 0]))
    add('used_induction_hypothesis', ['i', induction, 0, step], induction)

    witness_goal = ['D', eq(2, 2)]
    witness_major = ['i', witness_goal, S(0), ['h', 0]]
    witness_branch = ['i', witness_goal, 1, ['q', 0, ['h', 0], ['h', 1]]]
    add('existential_witness_reused_in_introduction',
        ['e', witness_goal, witness_major, witness_branch], witness_goal)
    compound = ['D', ['D', eq(1, 1)]]
    add('compound_case_introduction', ['i', compound, 0, ['h', 0]], compound)
    # A non-literal zero witness uses the case mode; its counter-zero
    # instance remains the alias while its successor instance computes to 0.
    alias = I(S(0), 0, 1)
    alias_goal = ['D', eq(I(1, 2, 0), 0)]
    alias_step = ['r', 1, general.shift(alias), 0]
    add('case_at_nonliteral_zero_alias', ['i', alias_goal, alias, alias_step], alias_goal)
    return result


def fixture_seed_direct():
    b = Builder('seed')
    result = {}

    def add(name, proof):
        result[name] = packet(b.conclusion(proof), proof)

    e = ['r', 0, 0, 1]
    source = I(S(0), 0, 1)
    add('direct_root_reflexivity', ['x', e, e])
    add('direct_slot_counter_two', ['x', e, ['r', S(0), source, S(1)]])
    add('direct_slot_nested_body', ['x', e, ['r', S(0), source, I(S(1), 1, S(2))]])
    major_zero = b.sym(e)
    add('direct_slot_zero_source', ['x', major_zero, ['r', 0, 0, S(1)]])
    return result


def negative_seed(positive):
    b = Builder('seed')
    e = ['r', 0, 0, 1]
    false = packet(eq(0, S(0)), b.refl(0))
    d = ['D', eq(1, 1)]
    dp = positive['progress_introduction']['proof']
    goal = eq(0, 0)
    items = {
        'false_closed_goal': false,
        'negative_variable': packet(eq(-1, -1), b.refl(0)),
        'boolean_variable': packet(eq(True, True), b.refl(0)),
        'float_variable': packet(eq(0.0, 0.0), b.refl(0)),
        'free_variable_goal': packet(eq(1, 1), b.refl(0)),
        'uncanonical_zero_counter': packet(eq([0, 0, 1], 0), b.refl(0)),
        'removed_zero_rule': packet(goal, ['z', 0, 1]),
        'unknown_rule': packet(goal, ['oracle']),
        'extra_rule_field': packet(goal, ['r', 0, 0, 1, 0]),
        'negative_hypothesis_index': packet(goal, ['h', -1]),
        'boolean_hypothesis_index': packet(goal, ['h', False]),
        'out_of_scope_computation_body': packet(goal, ['r', 0, 0, 2]),
        'non_equation_major': packet(goal, ['x', dp, e]),
        'non_equation_minor': packet(goal, ['x', e, dp]),
        'scalar_minor_is_not_source': packet(goal, ['x', e, b.refl(0)]),
        'successor_minor_has_no_initializer': packet(goal, ['x', e, b.refl(S(0))]),
        'wrong_iterator_initializer': packet(goal, ['x', e, ['r', 0, S(0), 1]]),
        'extra_transport_template': packet(goal, ['x', 1, e, e]),
        'future_WI_witness': packet(d, ['i', d, 1, ['h', 0]]),
        'future_WI_witness_under_binder': packet(d, ['i', d, I(S(0), 0, 2), ['h', 0]]),
        'DE_eigenparameter_escape': packet(goal, ['e', eq(1, 1), dp, ['h', 0]]),
        'Q_target_out_of_scope': packet(goal, ['q', 1, positive['existential_to_closure']['proof'], b.refl(0)]),
        'wrong_Q_base': packet(goal, ['q', 0, positive['existential_to_closure']['proof'], e]),
        'nonzero_witness_cannot_force_progress': packet(
            positive['used_induction_hypothesis']['goal'],
            ['i', positive['used_induction_hypothesis']['goal'], S(0), positive['used_induction_hypothesis']['proof'][3]]),
    }
    extra = dict(positive['reflexivity_zero'])
    extra['trusted'] = True
    items['extra_top_level_field'] = extra
    return items


def negative_general(positive):
    b = Builder('general')
    e = ['r', 0, 0, 1]
    d = positive['progress_introduction']['proof']
    goal = eq(0, 0)
    extra = dict(positive['reflexivity_zero'])
    extra['trusted'] = True
    return {
        'false_closed_goal': packet(eq(0, S(0)), b.refl(0)),
        'non_equation_major': packet(goal, ['x', 1, d, e]),
        'non_equation_minor': packet(goal, ['x', 1, e, d]),
        'out_of_scope_template': packet(goal, ['x', 2, e, e]),
        'boolean_template': packet(goal, ['x', True, e, e]),
        'wrong_template_left': packet(goal, ['x', S(1), e, e]),
        'extra_transport_field': packet(goal, ['x', 1, e, e, 0]),
        'unknown_rule': packet(goal, ['oracle']),
        'free_variable_goal': packet(eq(1, 1), b.refl(0)),
        'extra_top_level_field': extra,
    }


def eval_term(t, env):
    if type(t) is int:
        return 0 if t == 0 else env[t - 1]
    if len(t) == 1:
        return eval_term(t[0], env) + 1
    counter, value = eval_term(t[0], env), eval_term(t[1], env)
    for _ in range(counter):
        value = eval_term(t[2], [value] + env)
    return value


def semantic_checks():
    terms = [0, 1, S(0), S(1), I(S(0), 1, 2), I(1, 0, S(1)),
             I(S(1), 1, S(1)), I(S(0), I(1, 0, S(1)), 2),
             I(I(1, 0, 1), S(1), S(1))]
    images = [0, 1, S(1), I(1, 0, S(1))]
    count = 0
    for t, image, value in itertools.product(terms, images, range(5)):
        assert general.term(t, 1) and general.term(image, 1)
        output = general.subst(t, [image])
        assert general.term(output, 1)
        assert output == seed.subst(t, [image])
        assert eval_term(output, [value]) == eval_term(t, [eval_term(image, [value])])
        count += 1
    assert general.subst(I(I(1, 0, 1), S(1), S(1)), [0]) == S(0)
    assert general.subst(I(S(0), 1, 2), [S(1)]) == I(S(0), S(1), S(2))
    assert general.subst(['D', ['Q', eq(1, 4)]], [S(1)]) == ['D', ['Q', eq(1, S(4))]]
    return {'independent_numerical_comparisons': count, 'nested_counter_normalization': True,
            'state_capture_avoidance': True, 'nested_formula_capture_avoidance': True}


def metrics(path):
    tree = ast.parse(path.read_text())
    if isinstance(tree.body[0], ast.Expr) and isinstance(tree.body[0].value, ast.Constant):
        tree.body.pop(0)
    normalized = ast.unparse(tree) + '\n'
    raw = normalized.encode()
    ignored = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE,
               tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}
    data = {'normalized_bytes': len(raw),
            'tokens': sum(t.type not in ignored for t in tokenize.tokenize(io.BytesIO(raw).readline)),
            'ast_nodes': sum(1 for _ in ast.walk(ast.parse(raw))),
            'gzip9': len(gzip.compress(raw, compresslevel=9, mtime=0)),
            'raw_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
    normalized_path = path.with_name(path.stem + '.normalized.py')
    normalized_path.write_text(normalized)
    normalized_path.with_suffix('.py.gz').write_bytes(gzip.compress(raw, compresslevel=9, mtime=0))
    return data, normalized_path


def run():
    old = fixture_general()
    new = {}
    translation_records = []
    for name, data in old.items():
        p = to_seed(data['proof'])
        assert seed.derive(p, [], 0) == data['goal']
        rt = to_general(p)
        assert general.derive(rt, [], 0) == data['goal']
        new[name] = packet(data['goal'], p)
        translation_records.append({'name': name, 'direction': 'general-seed-general', 'same_goal': True,
                                    'old_json_bytes': len(json.dumps(data)),
                                    'seed_json_bytes': len(json.dumps(new[name]))})
    direct = fixture_seed_direct()
    for name, data in direct.items():
        p = to_general(data['proof'])
        rt = to_seed(p)
        assert general.derive(p, [], 0) == seed.derive(rt, [], 0) == data['goal']
        new[name] = data
        old[name] = packet(data['goal'], p)
        translation_records.append({'name': name, 'direction': 'seed-general-seed', 'same_goal': True})

    # Both parameters in this slot context contain the same variable that
    # is being equated to zero; neither parameter is rewritten by SeedTr.
    context = [eq(1, 0)]
    op = ['x', ['h', 0], ['r', 1, 1, S(2)]]
    wanted = eq(I(S(1), 0, S(2)), S(1))
    assert seed.derive(op, context, 1) == wanted
    gp = to_general(op, context, 1)
    assert general.derive(gp, context, 1) == wanted
    assert seed.derive(to_seed(gp, context, 1), context, 1) == wanted
    open_data = {'scope': 1, 'context': context, 'goal': wanted, 'proof': op}
    (ROOT / 'open_parameter_certificate.json').write_text(json.dumps(open_data, indent=2) + '\n')

    neg = negative_seed(new)
    results = {'python': sys.version, 'metrics': {}, 'closed_translation_checks': translation_records,
               'open_parameter_translation': True, 'substitution': semantic_checks(), 'process_checks': []}
    for name in ('general_context', 'seed_checked', 'seed_only'):
        path = ROOT / (name + '.py')
        met, normalized = metrics(path)
        results['metrics'][name] = met
        positive = old if name == 'general_context' else new
        negative = negative_general(old) if name == 'general_context' else neg
        for expectation, items in [(True, positive), (False, negative)]:
            for label, data in items.items():
                dest = ROOT / 'certificates' / name / (label + '.json')
                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_text(json.dumps(data, separators=(',', ':')) + '\n')
                for executable in (path, normalized):
                    for optimized in (False, True):
                        cmd = [sys.executable] + (['-O'] if optimized else []) + [str(executable)]
                        proc = subprocess.run(cmd, input=json.dumps(data), text=True, capture_output=True, timeout=20)
                        accepted = proc.returncode == 0 and proc.stdout == 'ACCEPT\n' and not proc.stderr
                        if accepted != expectation or (not expectation and proc.stdout != 'REJECT\n'):
                            raise RuntimeError((name, label, optimized, proc.returncode, proc.stdout, proc.stderr))
                        results['process_checks'].append({'checker': executable.name, 'case': label,
                                                         'optimized': optimized, 'expected': expectation,
                                                         'accepted': accepted})
    (ROOT / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
    print(json.dumps({'metrics': results['metrics'], 'closed_positive_cases': len(new),
                      'seed_negative_cases': len(neg), 'general_negative_cases': len(negative_general(old)), 'translation_round_trips': len(translation_records),
                      'process_checks': len(results['process_checks']), 'substitution': results['substitution']}, indent=2))


if __name__ == '__main__':
    run()

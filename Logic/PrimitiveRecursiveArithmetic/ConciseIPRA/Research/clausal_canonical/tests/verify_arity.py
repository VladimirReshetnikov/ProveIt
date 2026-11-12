"""Untrusted representation translations, certificates, and matched controls."""
import copy
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tests'))
import verify_clausal as C

base = C.base
OUTPUT = C.OUTPUT
arity = C.load('arity_primary', OUTPUT / 'arity_checker.py')
producer = C.load('arity_producer', OUTPUT / 'translate_arity.py')
CONTROL = OUTPUT.parent / 'comparison/arity_current_control.py'
control = C.load('arity_control', CONTROL)


def decode_term(a, scope, depth=0):
    if type(a) is int:
        return a + depth + scope + 1 if a < 0 else a
    return [decode_term(a[0], scope, depth), decode_term(a[1], scope, depth),
            decode_term(a[2], scope, depth + 1)]


def decode_formula(a, scope, depth=0):
    if len(a) == 2:
        return ['=', decode_term(a[0], scope, depth), decode_term(a[1], scope, depth)]
    return ['D', decode_formula(a[0], scope, depth + 2)]


def decode_proof(p, scope=0):
    tag = p[0]
    if tag == 'u':
        return [tag, p[1], decode_term(p[2], scope), decode_proof(p[3], scope)]
    if tag == 'r':
        return [tag, decode_term(p[1], scope), decode_term(p[2], scope),
                decode_term(p[3], scope, 1)]
    if tag == 'x':
        return [tag, decode_term(p[1], scope, 1), decode_proof(p[2], scope),
                decode_proof(p[3], scope)]
    if tag == 'e':
        return [tag, decode_formula(p[1], scope), decode_proof(p[2], scope),
                decode_proof(p[3], scope + 1)]
    if tag == 'i':
        return [tag, decode_formula(p[1], scope), decode_term(p[2], scope),
                decode_proof(p[3], scope + 1)]
    raise ValueError('unknown arity rule')


def decode(data):
    return {'goal': decode_formula(data['goal'], 0), 'proof': decode_proof(data['proof'])}


def control_term(a, scope, depth=0):
    """Convert valid syntax exactly; preserve tested malformed-index attacks.

The two extra inequalities keep an invalid source index outside the target
scope instead of accidentally converting an out-of-scope index to zero.
They are test-producer safeguards, not trusted kernel code.
"""
    if type(a) is int:
        if a < 0:
            return -scope - 1
        if a > scope + depth:
            return depth + 1
        return a if a <= depth else a - depth - scope - 1
    if type(a) is not list or len(a) != 3:
        return copy.deepcopy(a)
    return [control_term(a[0], scope, depth), control_term(a[1], scope, depth),
            control_term(a[2], scope, depth + 1)]


def control_formula(a, scope, depth=0):
    if type(a) is not list or not a:
        return copy.deepcopy(a)
    if a[0] == '=' and len(a) == 3:
        return [control_term(a[1], scope, depth), control_term(a[2], scope, depth)]
    if a[0] == 'Q' and len(a) == 2:
        return ['Q', control_formula(a[1], scope, depth + 1)]
    if a[0] == 'D' and len(a) == 2:
        return [control_formula(a[1], scope, depth + 2)]
    return copy.deepcopy(a)


def control_proof(p, scope=0):
    if type(p) is not list or not p or len(p) < 4:
        return copy.deepcopy(p)
    tag = p[0]
    tail = copy.deepcopy(p[4:])
    if tag == 'r':
        result = [tag, control_term(p[1], scope), control_term(p[2], scope),
                  control_term(p[3], scope, 1)]
    elif tag == 'x':
        result = [tag, control_formula(p[1], scope, 1), control_proof(p[2], scope),
                  control_proof(p[3], scope)]
    elif tag == 'q':
        result = [tag, control_term(p[1], scope), control_proof(p[2], scope),
                  control_proof(p[3], scope)]
    elif tag == 'e':
        result = [tag, control_formula(p[1], scope), control_proof(p[2], scope),
                  control_proof(p[3], scope + 1)]
    elif tag == 'i':
        result = [tag, control_formula(p[1], scope), control_term(p[2], scope),
                  control_proof(p[3], scope + 1)]
    else:
        return copy.deepcopy(p)
    return result + tail


def control_certificate(data):
    result = copy.deepcopy(data)
    result['goal'] = control_formula(data['goal'], 0)
    result['proof'] = control_proof(data['proof'])
    return result


def negative_cases(positive):
    packet, S = base.packet, arity.successor
    ref = positive['reflexivity_zero']['proof']
    H = ['r', 0, 0, 0]
    bad = {
        'false_goal': packet([0, S(0)], ref),
        'boolean_term': packet([True, True], ref),
        'float_term': packet([0.0, 0.0], ref),
        'unbound_positive_goal': packet([1, 1], ref),
        'unbound_negative_goal': packet([-1, -1], ref),
        'noncanonical_goal': packet([[0, 0, 1], S(0)], ref),
        'first_class_Q_forbidden': packet(['Q', [1, 1]], ref),
        'old_hyp_rule_forbidden': packet([0, 0], ['h', 0]),
        'old_qe_rule_forbidden': packet([0, 0], ['q', 0, ref, ref]),
        'old_zero_rule_forbidden': packet([S(0), S(0)], ['z', 0, 0]),
        'use_empty_context': packet([0, 0], ['u', 0, 0, H]),
        'extra_rule_field': packet([0, 0], ['r', 0, 0, 0, 0]),
        'extra_top_level_field': dict(positive['reflexivity_zero'], oracle=True),
        'recursor_body_scope': packet([0, 0], ['r', 0, 0, 2]),
        'term_template_scope': packet([0, 0], ['x', 2, H, ref]),
        'term_template_fresh_level': packet([0, 0], ['x', -1, H, ref]),
        'equation_template_forbidden': packet([0, 0], ['x', [1, 1], H, ref]),
        'wrong_template_instance': packet([0, 0], ['x', S(1), H, ref]),
    }
    ordinary = [[[1, 1]]]
    bad['use_bad_neutral_premise'] = packet(ordinary,
        ['i', ordinary, 0, ['u', 0, 0, ref]])
    bad['use_boolean_index'] = packet(ordinary,
        ['i', ordinary, 0, ['u', True, 0, H]])
    bad['use_negative_index'] = packet(ordinary,
        ['i', ordinary, 0, ['u', -1, 0, H]])
    bad['use_future_index'] = packet(ordinary,
        ['i', ordinary, 0, ['u', 1, 0, H]])
    bad['use_unbound_positive_witness'] = packet(ordinary,
        ['i', ordinary, 0, ['u', 0, 1, H]])
    bad['use_future_level_witness'] = packet(ordinary,
        ['i', ordinary, 0, ['u', 0, -2, H]])
    bad['intro_future_level_witness'] = packet(ordinary,
        ['i', ordinary, -1, ['u', 0, 0, H]])
    bad['intro_noncanonical_witness'] = packet(ordinary,
        ['i', ordinary, [0, 0, 1], ['u', 0, 0, H]])
    bad['intro_equation_goal'] = packet([0, 0], ['i', [0, 0], 0, ref])
    bad['elim_nonpaired_major'] = packet([0, 0], ['e', [0, 0], ref, ref])
    paired = positive['progress_introduction']['proof']
    bad['elim_parameter_escape'] = packet([0, 0],
        ['e', [-1, -1], paired, ['u', 0, 0, H]])
    bad['wrong_minor_root'] = packet([0, 0], ['x', 1, H, paired])
    bad['wrong_major_root'] = packet([0, 0], ['x', 1, paired, ref])
    bad['nonzero_witness_cannot_force_progress'] = copy.deepcopy(positive['used_induction_hypothesis'])
    bad['nonzero_witness_cannot_force_progress']['proof'][2] = S(0)
    return bad


def run():
    tagged = {p.stem: json.loads(p.read_text()) for p in (ROOT / 'evidence/clausal_certificates').glob('*.json')}
    names = [r['name'] for r in json.loads((ROOT / 'evidence/clausal_results.json').read_text())['certificates']
             if r['expected'] == 'ACCEPT']
    positive = {name: producer.translate(tagged[name]) for name in names}
    negative = negative_cases(positive)
    metrics = {'primary': base.measure(OUTPUT / 'arity_checker.py'),
               'same_representation_current_control': base.measure(CONTROL)}
    records = []
    for expected, collection in ((True, positive), (False, negative)):
        for name, data in collection.items():
            destination = ROOT / 'evidence/arity_certificates' / (name + '.json')
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_text(json.dumps(data, separators=(',', ':')) + '\n')
            for path in (OUTPUT / 'arity_checker.py', OUTPUT / 'arity_checker.normalized.py'):
                for optimized in (False, True):
                    base.cli(path, data, expected, optimized)
            if expected:
                decoded = decode(data)
                assert decoded == tagged[name], name
                C.cl.verify(decoded)
                translated = C.clausal_to_native(decoded['proof'])
                base.cli(C.BASELINE_PATH, base.packet(decoded['goal'], base.new_to_old(translated)), True)
            records.append({'name': name, 'expected': 'ACCEPT' if expected else 'REJECT'})
    baseline_positive, baseline_negative = base.controls.cases(base.old, 'canonical')
    control_records = []
    for expected, collection in ((True, baseline_positive), (False, baseline_negative)):
        for name, data in collection.items():
            converted = control_certificate(data)
            destination = ROOT / 'evidence/control_certificates' / (name + '.json')
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_text(json.dumps(converted, separators=(',', ':')) + '\n')
            for path in (CONTROL, CONTROL.with_suffix('.normalized.py')):
                for optimized in (False, True):
                    base.cli(path, converted, expected, optimized)
            control_records.append({'name': name, 'expected': 'ACCEPT' if expected else 'REJECT'})
    result = {'python': sys.version, 'metrics': metrics,
              'primary_positive_certificates': len(positive), 'primary_negative_certificates': len(negative),
              'primary_cli_checks': 4 * (len(positive) + len(negative)),
              'primary_reverse_translation_to_baseline_cli_checks': len(positive),
              'control_positive_certificates': len(baseline_positive),
              'control_negative_certificates': len(baseline_negative),
              'control_cli_checks': 4 * (len(baseline_positive) + len(baseline_negative)),
              'certificates': records, 'control_certificates': control_records,
              'scope': 'Finite executable checks and explicit proof translations, not proof-assistant verification.'}
    (ROOT / 'evidence/arity_results.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('certificates', 'control_certificates')}, indent=2))


if __name__ == '__main__':
    run()

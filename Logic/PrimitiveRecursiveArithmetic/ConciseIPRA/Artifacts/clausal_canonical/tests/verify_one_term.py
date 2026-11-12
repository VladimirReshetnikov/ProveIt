"""Untrusted certificates and derivation translations for one-term canonical R.

The standalone native comparison checker is comparison/unrestricted_checker.py.  This file is a producer
and regression harness, not part of its trusted acceptance implementation.
"""
import ast
import copy
import gzip
import hashlib
import importlib.util
import io
import json
import subprocess
import sys
import tokenize
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'comparison'
CODE = ROOT / 'comparison'


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


old = load('canonical_baseline', BASE / 'canonical_checker.py')
restricted = load('canonical_one_term', CODE / 'restricted_checker.py')
new = load('canonical_unrestricted', CODE / 'unrestricted_checker.py')
controls = load('baseline_controls', BASE / 'upstream_test_family.py')


def eq(a, b):
    return ['=', a, b]


def packet(goal, proof):
    return {'goal': goal, 'proof': proof}


def new_refl(t):
    leaf = ['r', 0, 0, new.shift_term(t)]
    return ['x', 1, leaf, leaf]


def new_sym(proof, context=(), scope=0):
    formula = new.derive(proof, list(context), scope)
    assert formula[0] == '='
    return ['x', new.shift_term(formula[1]), ['r', 0, 0, 0], proof]


def old_sym(proof, context=(), scope=0):
    formula = old.derive(proof, list(context), scope)
    assert formula[0] == '='
    return ['x', old.shift_formula(formula), ['r', 0, 0, 0], proof]


def reflexive_formula(formula, context_size=0):
    """Prove nested Q/D formulas whose leaves are literal reflexivities.

This deliberately creates scopes in which Q and recursor binders overlap;
it supplies independent binder-conversion controls for the later codecs.
"""
    if formula[0] == '=':
        assert formula[1] == formula[2]
        return new_refl(formula[1])
    if formula[0] == 'Q':
        paired = ['D', new.shift_formula(formula[1], 1, 1)]
        return ['e', formula, reflexive_formula(paired, context_size),
                ['h', context_size]]
    body = new.shift_formula(formula[1], 1, 2)
    target = new.subst_formula(body, [new.successor(1), 0])
    return ['i', formula, 0, reflexive_formula(target, context_size + 1)]


def branch_context(proof, context, scope):
    """The same shifted context is used by both calculi's e and i rules."""
    if proof[0] == 'e':
        paired = old.derive(proof[2], context, scope)
        return [old.shift_formula(a) for a in context] + [['Q', paired[1]]]
    goal, witness = proof[1:3]
    body = old.shift_formula(goal[1], 1, 2)
    eta = 1 if goal[1][0] == '=' and witness == 0 else 0
    hypothesis = old.subst_formula(body, [eta, old.shift_term(witness)])
    return [old.shift_formula(a) for a in context] + [hypothesis]


def old_to_new(proof, context=(), scope=0):
    """Translate every valid baseline proof, preserving its conclusion."""
    context = list(context)
    tag = proof[0]
    if tag in ('h', 'r'):
        result = copy.deepcopy(proof)
    elif tag == 'x':
        template, major, minor = proof[1:]
        major = old_to_new(major, context, scope)
        minor = old_to_new(minor, context, scope)
        first = ['x', template[1], major, minor]
        second = ['x', template[2], major, first]
        result = new_sym(second, context, scope)
    elif tag == 'q':
        result = ['q', proof[1], old_to_new(proof[2], context, scope),
                  old_to_new(proof[3], context, scope)]
        if new.derive(result, context, scope)[0] == '=':
            result = new_sym(result, context, scope)
    elif tag == 'e':
        extended = branch_context(proof, context, scope)
        result = ['e', proof[1], old_to_new(proof[2], context, scope),
                  old_to_new(proof[3], extended, scope + 1)]
    elif tag == 'i':
        extended = branch_context(proof, context, scope)
        result = ['i', proof[1], proof[2],
                  old_to_new(proof[3], extended, scope + 1)]
    else:
        raise ValueError('unknown baseline rule')
    assert new.derive(result, context, scope) == old.derive(proof, context, scope)
    return result


def restricted_to_old(proof, context=(), scope=0):
    """Translate every valid restricted one-term proof into the baseline."""
    context = list(context)
    tag = proof[0]
    if tag in ('h', 'r'):
        result = copy.deepcopy(proof)
    elif tag == 'x':
        template, major, minor = proof[1:]
        right = new.derive(minor, context, scope)[2]
        result = ['x', eq(template, new.shift_term(right)),
                  restricted_to_old(major, context, scope), restricted_to_old(minor, context, scope)]
    elif tag == 'q':
        result = ['q', proof[1], restricted_to_old(proof[2], context, scope),
                  restricted_to_old(proof[3], context, scope)]
        if old.derive(result, context, scope)[0] == '=':
            result = old_sym(result, context, scope)
    elif tag == 'e':
        paired = new.derive(proof[2], context, scope)
        extended = [new.shift_formula(a) for a in context] + [['Q', paired[1]]]
        result = ['e', proof[1], restricted_to_old(proof[2], context, scope),
                  restricted_to_old(proof[3], extended, scope + 1)]
    elif tag == 'i':
        extended = branch_context(proof, context, scope)
        result = ['i', proof[1], proof[2],
                  restricted_to_old(proof[3], extended, scope + 1)]
    else:
        raise ValueError('unknown one-term rule')
    assert old.derive(result, context, scope) == new.derive(proof, context, scope)
    return result


def restricted_trans(left, right, context, scope):
    """Compose a=b and b=c using restricted one-term transport only."""
    a, b = restricted.derive(left, context, scope)[1:]
    middle, c = restricted.derive(right, context, scope)[1:]
    assert middle == b
    if b != 0:
        return ['x', 1, right, new_sym(left, context, scope)]
    if a == 0:
        return right
    if c == 0:
        return left
    # Join each nonzero term proved equal to 0 to the nonzero anchor J(0).
    j_template = restricted.rec(restricted.successor(0), 0, 2)
    a_anchor = ['x', j_template, left, ['r', 0, 0, restricted.shift_term(a)]]
    c_zero = new_sym(right, context, scope)
    c_anchor = ['x', j_template, c_zero, ['r', 0, 0, restricted.shift_term(c)]]
    return ['x', 1, new_sym(c_anchor, context, scope), new_sym(a_anchor, context, scope)]


def restricted_full_transport(template, major, minor, context, scope):
    """Expand an unrestricted Tr instance through equality congruence."""
    s, t = restricted.derive(major, context, scope)[1:]
    if s != 0:
        return ['x', template, major, minor]
    hs = restricted.subst_term(template, [s])
    ht = restricted.subst_term(template, [t])
    if t == 0:
        congruence = new_refl(hs)
    else:
        backward = ['x', template, new_sym(major, context, scope), new_refl(ht)]
        congruence = new_sym(backward, context, scope)
    return restricted_trans(new_sym(minor, context, scope), congruence, context, scope)


def new_to_restricted(proof, context=(), scope=0):
    """Remove all literal-zero transport sources by explicit proof expansion."""
    context = list(context)
    tag = proof[0]
    if tag in ('h', 'r'):
        result = copy.deepcopy(proof)
    elif tag == 'x':
        template, major, minor = proof[1:]
        result = restricted_full_transport(template,
            new_to_restricted(major, context, scope),
            new_to_restricted(minor, context, scope), context, scope)
    elif tag == 'q':
        result = ['q', proof[1], new_to_restricted(proof[2], context, scope),
                  new_to_restricted(proof[3], context, scope)]
    elif tag == 'e':
        paired = new.derive(proof[2], context, scope)
        extended = [new.shift_formula(a) for a in context] + [['Q', paired[1]]]
        result = ['e', proof[1], new_to_restricted(proof[2], context, scope),
                  new_to_restricted(proof[3], extended, scope + 1)]
    elif tag == 'i':
        extended = branch_context(proof, context, scope)
        result = ['i', proof[1], proof[2],
                  new_to_restricted(proof[3], extended, scope + 1)]
    else:
        raise ValueError('unknown one-term rule')
    assert restricted.derive(result, context, scope) == new.derive(proof, context, scope)
    return result


def new_to_old(proof, context=(), scope=0):
    return restricted_to_old(new_to_restricted(proof, context, scope), context, scope)


def cases():
    S, R = new.successor, new.rec
    J = lambda t: R(S(0), 0, new.shift_term(t))
    positive = {
        'successor_computation': packet(eq(J(0), 0), ['r', 0, 0, 0]),
        'reflexivity_zero': packet(eq(0, 0), new_refl(0)),
        'reflexivity_successor': packet(eq(S(0), S(0)), new_refl(S(0))),
        'symmetry_constant_template': packet(eq(0, J(0)), new_sym(['r', 0, 0, 0])),
    }
    d_refl = ['D', eq(1, 1)]
    d_refl_proof = ['i', d_refl, 0, new_refl(S(1))]
    q_refl = ['Q', d_refl[1]]
    q_refl_proof = ['e', q_refl, d_refl_proof, ['h', 0]]
    positive['progress_introduction'] = packet(d_refl, d_refl_proof)
    positive['paired_elimination_to_closure'] = packet(q_refl, q_refl_proof)
    positive['closure_elimination'] = packet(eq(S(S(0)), S(S(0))),
        ['q', S(S(0)), q_refl_proof, new_refl(0)])

    # The step uses its retained arithmetic induction hypothesis, not a
    # reflexive equation or an unused-assumption shortcut.
    induction = ['D', eq(R(1, 0, S(1)), S(1))]
    ih = eq(R(1, 0, S(1)), S(1))
    reverse_computation = new_sym(['r', 1, 0, S(1)], [ih], 1)
    step = ['x', S(1), ['h', 0], reverse_computation]
    positive['used_induction_hypothesis'] = packet(induction,
        ['i', induction, 0, step])

    j_body = eq(R(S(0), 0, 2), 1)
    j_d = ['D', j_body]
    j_d_proof = ['i', j_d, 0, ['r', 0, 0, new.shift_term(S(1))]]
    j_q = ['Q', j_body]
    j_q_proof = ['e', j_q, j_d_proof, ['h', 0]]
    positive['ordinary_closure_direction'] = packet(eq(J(S(0)), S(0)),
        ['q', S(0), j_q_proof, ['r', 0, 0, 0]])

    witness_goal = ['D', eq(2, 2)]
    witness_major = ['i', witness_goal, S(0), ['h', 0]]
    witness_branch = ['i', witness_goal, 1, ['q', 0, ['h', 0], ['h', 1]]]
    positive['paired_witness_and_shifted_context'] = packet(witness_goal,
        ['e', witness_goal, witness_major, witness_branch])
    compound = ['D', ['D', eq(1, 1)]]
    positive['compound_case_introduction'] = packet(compound,
        ['i', compound, 0, ['h', 0]])

    # Normalizing substitution erases the update only after the equality's
    # target endpoint 0 is substituted for the template's counter variable.
    template = R(1, 0, S(1))
    source = R(J(0), 0, S(1))
    positive['zero_counter_exposed_by_transport'] = packet(eq(source, S(0)),
        ['x', template, ['r', 0, 0, 0], new_refl(source)])
    positive['template_uses_context_parameter'] = packet(
        ['D', eq(R(S(0), 0, 2), 1)], j_d_proof)
    positive['zero_source_transport'] = packet(eq(0, 0),
        ['x', 1, new_refl(0), new_refl(0)])
    zero_anchor = new_sym(['r', 0, 0, 0])
    positive['zero_source_nontrivial_target'] = packet(eq(S(0), S(J(0))),
        ['x', S(1), zero_anchor, new_refl(S(0))])
    positive['zero_source_canonical_counter'] = packet(eq(S(0), source),
        ['x', template, zero_anchor, new_refl(S(0))])
    nested_terms = R(2, 0, S(1))
    nested_formulas = {
        'Q_inside_D_parameter': ['D', ['Q', eq(2, 2)]],
        'D_inside_Q_parameter': ['Q', ['D', eq(3, 3)]],
        'D_Q_D_nested_parameter': ['D', ['Q', ['D', eq(4, 4)]]],
        'Q_Q_recursor_binders': ['Q', ['Q', eq(nested_terms, nested_terms)]],
    }
    for name, formula in nested_formulas.items():
        positive[name] = packet(formula, reflexive_formula(formula))
    q_hyp = ['D', ['Q', eq(1, 1)]]
    positive['ordinary_Q_hypothesis'] = packet(q_hyp, ['i', q_hyp, 0, ['h', 0]])

    negative = {
        'false_goal': packet(eq(0, S(0)), new_refl(0)),
        'negative_index': packet(eq(-1, -1), new_refl(0)),
        'boolean_is_not_integer': packet(eq(True, True), new_refl(0)),
        'float_is_not_integer': packet(eq(0.0, 0.0), new_refl(0)),
        'future_witness': packet(witness_goal, ['i', witness_goal, 1, ['h', 0]]),
        'future_witness_inside_body': packet(witness_goal,
            ['i', witness_goal, R(S(0), 0, 2), ['h', 0]]),
        'recursor_body_out_of_scope': packet(eq(0, 0), ['r', 0, 0, 2]),
        'equation_is_not_term_template': packet(eq(0, 0),
            ['x', eq(1, 1), ['r', 0, 0, 0], new_refl(0)]),
        'compound_transport_template': packet(eq(0, 0),
            ['x', ['Q', eq(1, 1)], ['r', 0, 0, 0], new_refl(0)]),
        'wrong_template_instance': packet(eq(0, 0),
            ['x', S(1), ['r', 0, 0, 0], new_refl(0)]),
        'wrong_minor_formula_root': packet(eq(0, 0),
            ['x', 1, ['r', 0, 0, 0], d_refl_proof]),
        'wrong_major_formula_root': packet(eq(0, 0),
            ['x', 1, d_refl_proof, new_refl(0)]),
        'wrong_closure_base': packet(eq(J(S(0)), S(0)),
            ['q', S(0), j_q_proof, new_refl(0)]),
        'eigenparameter_escapes_DE': packet(eq(0, 0),
            ['e', eq(1, 1), witness_major, ['h', 0]]),
        'nonzero_witness_cannot_force_progress': packet(induction,
            ['i', induction, S(0), step]),
        'unknown_rule': packet(eq(0, 0), ['oracle', eq(0, 0)]),
        'extra_rule_field': packet(eq(0, 0), ['r', 0, 0, 0, 0]),
        'extra_top_level_field': dict(positive['reflexivity_zero'], trusted=True),
        'noncanonical_zero_body_goal': packet(eq([0, 0, S(0)], S(0)), new_refl(S(0))),
        'noncanonical_zero_body_witness': packet(witness_goal,
            ['i', witness_goal, [0, 0, 1], ['h', 0]]),
        'removed_zero_rule': packet(eq(S(0), S(0)), ['z', 0, 1]),
        'hypothesis_index_boolean': packet(eq(0, 0), ['h', True]),
        'free_variable_template': packet(eq(0, 0),
            ['x', 2, ['r', 0, 0, 0], new_refl(0)]),
    }
    return positive, negative


def measure(path):
    source = path.read_bytes()
    tree = controls.RemoveDocstrings().visit(ast.parse(source))
    data = (ast.unparse(ast.fix_missing_locations(tree)) + '\n').encode()
    norm_path = path.with_suffix('.normalized.py')
    norm_path.write_bytes(data)
    compressed = gzip.compress(data, compresslevel=9, mtime=0)
    norm_path.with_suffix('.py.gz').write_bytes(compressed)
    ignored = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE,
               tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}
    return {'raw_bytes': len(source), 'normalized_bytes': len(data),
            'significant_tokens': sum(t.type not in ignored for t in tokenize.tokenize(io.BytesIO(data).readline)),
            'ast_nodes': sum(1 for _ in ast.walk(ast.parse(data))),
            'gzip9_bytes': len(compressed), 'sha256': hashlib.sha256(source).hexdigest(),
            'normalized_sha256': hashlib.sha256(data).hexdigest()}


def cli(path, certificate, expected, optimized=False):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(path)]
    process = subprocess.run(command, input=json.dumps(certificate), text=True,
                             capture_output=True, timeout=10)
    wanted = (0, 'ACCEPT\n', '') if expected else (1, 'REJECT\n', '')
    got = (process.returncode, process.stdout, process.stderr)
    if got != wanted:
        raise RuntimeError(f'{path.name}: {got!r}, wanted {wanted!r}')


def run():
    positive, negative = cases()
    baseline_positive, baseline_negative = controls.cases(old, 'canonical')
    for name, data in baseline_positive.items():
        positive['translated_baseline_' + name] = packet(data['goal'], old_to_new(data['proof']))
    metrics = {'baseline': measure(BASE / 'canonical_checker.py'),
               'one_term_restricted': measure(CODE / 'restricted_checker.py'),
               'one_term_unrestricted': measure(CODE / 'unrestricted_checker.py')}
    paths = [CODE / 'unrestricted_checker.py', CODE / 'unrestricted_checker.normalized.py']
    records = []
    for expected, collection in ((True, positive), (False, negative)):
        for name, data in collection.items():
            destination = ROOT / 'evidence/one_term_certificates' / (name + '.json')
            destination.parent.mkdir(parents=True, exist_ok=True)
            payload = json.dumps(data, separators=(',', ':')) + '\n'
            destination.write_text(payload)
            for path in paths:
                for optimized in (False, True):
                    cli(path, data, expected, optimized)
            if expected:
                reverse_translation = packet(data['goal'], new_to_old(data['proof']))
                cli(BASE / 'canonical_checker.py', reverse_translation, True)
            records.append({'name': name, 'expected': 'ACCEPT' if expected else 'REJECT',
                            'sha256': hashlib.sha256(payload.encode()).hexdigest()})
    for data in baseline_negative.values():
        cli(BASE / 'canonical_checker.py', data, False)
    substitution = controls.substitution_checks(new, 'canonical')
    result = {'python': sys.version, 'scope': 'Finite executable checks, not proof-assistant verification.',
              'metrics': metrics, 'positive_certificates': len(positive),
              'negative_certificates': len(negative),
              'candidate_cli_checks': 4 * (len(positive) + len(negative)),
              'reverse_translation_cli_checks': len(positive),
              'inherited_negative_controls': len(baseline_negative),
              'substitution': substitution, 'certificates': records}
    (ROOT / 'evidence/one_term_results.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'certificates'}, indent=2))


if __name__ == '__main__':
    run()

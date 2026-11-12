"""Reproduce named certificates, scope attacks, independent arithmetic checks and metrics.

This is untrusted test/producer code, separate from each standalone checker.
Finite tests supplement the written proof; they are not a formalization of it.
"""
import ast
import gzip
import hashlib
import importlib.util
import io
import itertools
import json
import subprocess
import sys
import tokenize
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def load(mode):
    spec = importlib.util.spec_from_file_location(mode, ROOT / (mode + '_checker.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def eq(a, b):
    return ['=', a, b]


def packet(goal, proof):
    return {'goal': goal, 'proof': proof}


def cases(module, mode):
    S, R = module.successor, module.rec

    def retract(t):
        return R(S(0), 0, module.shift_term(t))

    def refl(t):
        computation = ['r', 0, 0, module.shift_term(t)]
        return ['x', eq(1, module.shift_term(t)), computation, computation]

    def reversal(a, proof):
        return ['x', module.shift_formula(a), ['r', 0, 0, 0], proof]

    def close(dgoal, dproof):
        qgoal = ['Q', dgoal[1]]
        return qgoal, ['e', qgoal, dproof, ['h', 0]]

    positive = {}
    positive['successor_computation'] = packet(
        eq(R(S(0), 0, 0), 0), ['r', 0, 0, 0])
    positive['derived_reflexivity_zero'] = packet(eq(0, 0), refl(0))
    positive['derived_reflexivity_successor'] = packet(eq(S(0), S(0)), refl(S(0)))
    positive['crossed_equation_direction'] = packet(
        eq(0, retract(0)), reversal(eq(retract(0), 0), ['r', 0, 0, 0]))

    d_refl = ['D', eq(1, 1)]
    d_refl_proof = ['i', d_refl, 0, refl(S(1))]
    positive['progress_introduction'] = packet(d_refl, d_refl_proof)
    q_refl, q_refl_proof = close(d_refl, d_refl_proof)
    positive['paired_elimination_to_closure'] = packet(q_refl, q_refl_proof)
    positive['closure_elimination'] = packet(
        eq(S(S(0)), S(S(0))), ['q', S(S(0)), q_refl_proof, refl(0)])

    # A real use of the equation-induction hypothesis.  The step computes
    # the next state and then rewrites that state using the retained hypothesis.
    rhs = 1 if mode == 'scalar' else S(1)
    induction = ['D', eq(R(1, 0, S(1)), rhs)]
    lhs_step = R(S(1), 0, S(1))
    crossed_step = ['x', eq(module.shift_term(lhs_step), S(1)),
                    ['h', 0], ['r', 1, 0, S(1)]]
    step = reversal(eq(S(rhs), lhs_step), crossed_step)
    induction_proof = ['i', induction, 0, step]
    positive['used_induction_hypothesis'] = packet(induction, induction_proof)

    # J(y)=y is not syntactically symmetric, so the expected output checks
    # that QX reverses an equation root, while leaving compound roots alone.
    j_body = eq(R(S(0), 0, 2), 1)
    j_d = ['D', j_body]
    j_d_proof = ['i', j_d, 0, ['r', 0, 0, module.shift_term(S(1))]]
    j_q, j_q_proof = close(j_d, j_d_proof)
    positive['crossed_closure_direction'] = packet(
        eq(S(0), retract(S(0))), ['q', S(0), j_q_proof, ['r', 0, 0, 0]])

    # DE introduces x; the next WI uses x as its witness.  Its premise uses
    # the shifted exported Q and its own local base, exercising both scopes.
    witness_goal = ['D', eq(2, 2)]
    witness_major = ['i', witness_goal, S(0), ['h', 0]]
    witness_branch = ['i', witness_goal, 1, ['q', 0, ['h', 0], ['h', 1]]]
    positive['paired_witness_and_shifted_context'] = packet(
        witness_goal, ['e', witness_goal, witness_major, witness_branch])

    # Compound WI always uses the zero case, even at witness zero.
    compound_goal = ['D', ['D', eq(1, 1)]]
    positive['compound_case_introduction'] = packet(compound_goal,
                                                   ['i', compound_goal, 0, ['h', 0]])

    # Substituting the major's right endpoint zero into the template exposes
    # an R zero counter.  Only canonical R erases its body at this point.
    z_template_term = R(1, 0, S(1))
    c = retract(0)
    z_source_term = R(c, 0, S(1))
    z_target_term = R(0, 0, S(1))
    positive['zero_counter_exposed_by_transport'] = packet(
        eq(z_target_term, z_target_term),
        ['x', eq(z_template_term, z_template_term), ['r', 0, 0, 0], refl(z_source_term)])
    if mode != 'canonical':
        positive['primitive_zero_computation'] = packet(
            eq(R(0, 0, 1), 0 if mode == 'scalar' else S(0)), ['z', 0, 1])

    negative = {}
    negative['false_goal'] = packet(eq(0, S(0)), refl(0))
    negative['future_witness'] = packet(witness_goal, ['i', witness_goal, 1, ['h', 0]])
    negative['negative_index'] = packet(eq(-1, -1), refl(0))
    negative['boolean_is_not_integer'] = packet(eq(True, True), refl(0))
    negative['float_is_not_integer'] = packet(eq(0.0, 0.0), refl(0))
    negative['recursor_body_out_of_scope'] = packet(eq(0, 0), ['r', 0, 0, 2])
    negative['future_witness_inside_body'] = packet(
        witness_goal, ['i', witness_goal, R(S(0), 0, 2), ['h', 0]])
    negative['zero_source_transport'] = packet(
        eq(0, 0), ['x', eq(0, 0), refl(0), refl(0)])
    negative['compound_transport_template'] = packet(
        eq(0, 0), ['x', ['Q', eq(1, 1)], ['r', 0, 0, 0], refl(0)])
    negative['wrong_closure_base'] = packet(
        eq(S(0), retract(S(0))), ['q', S(0), j_q_proof, refl(0)])
    negative['eigenparameter_escapes_DE'] = packet(
        eq(0, 0), ['e', eq(1, 1), witness_major, ['h', 0]])
    negative['nonzero_witness_cannot_force_progress'] = packet(
        induction, ['i', induction, S(0), step])
    negative['unknown_rule'] = packet(eq(0, 0), ['oracle', eq(0, 0)])
    negative['extra_rule_field'] = packet(eq(0, 0), ['r', 0, 0, 0, 0])
    negative['extra_top_level_field'] = dict(positive['derived_reflexivity_zero'], trusted=True)
    if mode == 'canonical':
        negative['noncanonical_zero_body_goal'] = packet(eq([0, 0, S(0)], S(0)), refl(S(0)))
        negative['noncanonical_zero_body_witness'] = packet(
            witness_goal, ['i', witness_goal, [0, 0, 1], ['h', 0]])
        negative['removed_zero_rule'] = packet(eq(S(0), S(0)), ['z', 0, 1])
    return positive, negative


def evaluate(t, values, mode):
    """Independent ordinary natural-number interpretation, only for tests."""
    if type(t) is int:
        return 0 if t == 0 else values[t - 1]
    if mode == 'scalar' and len(t) == 1:
        return evaluate(t[0], values, mode) + 1
    n = evaluate(t[0], values, mode)
    state = evaluate(t[1], values, mode) + (mode != 'scalar')
    for _ in range(n):
        state = evaluate(t[2], [state] + values, mode)
    return state


def substitution_checks(module, mode):
    S, R = module.successor, module.rec
    exposed = module.subst_term([1, 0, S(1)], [0])
    expected = R(0, 0, S(1))
    if exposed != expected:
        raise RuntimeError('zero-counter normalization failure')
    nested = R(S(0), 1, 2)
    substituted = module.subst_term(nested, [S(1)])
    if substituted != R(S(0), S(1), S(2)):
        raise RuntimeError('capture in recursor body')
    f = ['D', ['Q', eq(1, 4)]]
    if module.subst_formula(f, [S(1)]) != ['D', ['Q', eq(1, S(4))]]:
        raise RuntimeError('capture across D and Q')

    terms = [0, 1, S(0), S(1), R(S(0), 1, 2), R(1, 0, S(1)),
             R(S(1), 1, S(1)), R(S(0), R(1, 0, S(1)), 2)]
    images = [0, 1, S(1), R(1, 0, S(1))]
    comparisons = 0
    for t, image, value in itertools.product(terms, images, range(5)):
        if not module.term(t, 1) or not module.term(image, 1):
            raise RuntimeError('invalid test term')
        got = module.subst_term(t, [image])
        if not module.term(got, 1):
            raise RuntimeError('substitution broke canonical well-formedness')
        if evaluate(got, [value], mode) != evaluate(t, [evaluate(image, [value], mode)], mode):
            raise RuntimeError('independent numerical substitution disagreement')
        comparisons += 1
    return {'zero_counter_after_substitution': True, 'recursor_capture': True,
            'nested_D_Q_capture': True, 'independent_evaluation_comparisons': comparisons}


class RemoveDocstrings(ast.NodeTransformer):
    def visit_Module(self, node):
        self.generic_visit(node)
        if node.body and isinstance(node.body[0], ast.Expr) and isinstance(node.body[0].value, ast.Constant) and isinstance(node.body[0].value.value, str):
            node.body.pop(0)
        return node

    visit_FunctionDef = visit_Module
    visit_AsyncFunctionDef = visit_Module
    visit_ClassDef = visit_Module


def measure(mode):
    path = ROOT / (mode + '_checker.py')
    raw = path.read_bytes()
    tree = RemoveDocstrings().visit(ast.parse(raw.decode('utf-8')))
    normalized = (ast.unparse(ast.fix_missing_locations(tree)) + '\n').encode('utf-8')
    norm_path = ROOT / (mode + '_checker.normalized.py')
    norm_path.write_bytes(normalized)
    compressed = gzip.compress(normalized, compresslevel=9, mtime=0)
    (ROOT / (mode + '_checker.normalized.py.gz')).write_bytes(compressed)
    ignored = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE,
               tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}
    return {'raw_bytes': len(raw), 'normalized_bytes_without_docstrings': len(normalized),
            'significant_tokens': sum(t.type not in ignored for t in tokenize.tokenize(io.BytesIO(normalized).readline)),
            'ast_nodes_without_docstrings': sum(1 for _ in ast.walk(ast.parse(normalized))),
            'normalized_gzip9_bytes': len(compressed), 'sha256': hashlib.sha256(raw).hexdigest(),
            'normalized_sha256': hashlib.sha256(normalized).hexdigest()}


def run():
    results = {'scope': 'Executable regression and independent finite arithmetic controls; no Lean verification.',
               'python': sys.version, 'modes': {}}
    for mode in ('canonical', 'raw', 'scalar'):
        module = load(mode)
        positive, negative = cases(module, mode)
        checks = substitution_checks(module, mode)
        records = []
        for expected, collection in [(True, positive), (False, negative)]:
            for name, data in collection.items():
                destination = ROOT / 'certificates' / mode / (name + '.json')
                destination.parent.mkdir(parents=True, exist_ok=True)
                payload = json.dumps(data, separators=(',', ':')) + '\n'
                destination.write_text(payload, encoding='utf-8')
                process = subprocess.run([sys.executable, str(ROOT / (mode + '_checker.py'))],
                                         input=payload, text=True, capture_output=True, timeout=10)
                accepted = process.returncode == 0 and process.stdout == 'ACCEPT\n' and not process.stderr
                if accepted != expected or (not expected and (process.returncode != 1 or process.stdout != 'REJECT\n' or process.stderr)):
                    raise RuntimeError(f'{mode}/{name}: expected {expected}, return {process.returncode}, stdout {process.stdout!r}, stderr {process.stderr!r}')
                records.append({'name': name, 'expected': 'ACCEPT' if expected else 'REJECT',
                                'actual': process.stdout.strip(), 'exit_code': process.returncode,
                                'sha256': hashlib.sha256(payload.encode()).hexdigest()})
        metrics = measure(mode)
        # Verify that docstring removal/ast.unparse preserves every named result.
        for expected, collection in [(True, positive), (False, negative)]:
            for name, data in collection.items():
                process = subprocess.run([sys.executable, str(ROOT / (mode + '_checker.normalized.py'))],
                                         input=json.dumps(data), text=True, capture_output=True, timeout=10)
                if (process.returncode == 0 and process.stdout == 'ACCEPT\n' and not process.stderr) != expected:
                    raise RuntimeError(f'normalization changed {mode}/{name}')
        results['modes'][mode] = {'rules': 6 if mode == 'canonical' else 7,
                                  'positive_certificates': len(positive), 'negative_certificates': len(negative),
                                  'substitution': checks, 'metrics': metrics, 'certificates': records}
    (ROOT / 'results.json').write_text(json.dumps(results, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({m: {k: v for k, v in r.items() if k != 'certificates'}
                      for m, r in results['modes'].items()}, indent=2))


if __name__ == '__main__':
    run()

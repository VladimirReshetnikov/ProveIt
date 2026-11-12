"""Untrusted proof builders, exact patch audit, metrics and CLI regressions.

Only checker.py is trusted by the new proof interface. This script constructs
finite certificates and checks their precise end sequents independently of
the general mathematical equivalence proof.
"""
import ast
import copy
import gzip
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent


def module(name, filename):
    spec = importlib.util.spec_from_file_location(name, ROOT / filename)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


K = module('uniform_raw_guarded', 'checker.py')
OLD = module('exception_raw_guarded', 'control_naming_exception.py')
UNRESTRICTED = module('unrestricted_raw_guarded', 'reference_unrestricted.py')


def S(t):
    return [0, t]


def I(n, a, h):
    return [n, a, h]


def C(n, a, b):
    return I(n, a, K.shift(b, 1))


def zero(a=0, h=0):
    return ['zero', a, h]


def succ(n, a, h):
    return ['succ', n, a, h]


def tr(template, p, q):
    return ['tr', template, p, q]


def refl(t):
    p = zero(t)
    return tr([1, t], p, p)


def result(p, clauses=(), scope=0):
    return K.infer(p, clauses, scope)


def sym(p, clauses=(), scope=0):
    s, t = result(p, clauses, scope)
    return tr([1, s], p, refl(s))


def trans(p, q, clauses=(), scope=0):
    s, t = result(p, clauses, scope)
    u, v = result(q, clauses, scope)
    if t != u:
        raise ValueError(('noncomposable equations', [s, t], [u, v]))
    return tr([s, 1], q, p)


def join(p, q, clauses=(), scope=0):
    return trans(p, sym(q, clauses, scope), clauses, scope)


def use(index, target=0, antecedent=None):
    return ['use', index, target, zero() if antecedent is None else antecedent]


def opened(matrix, b):
    body = K.sub(matrix, b, 2)
    return K.sub(body, 0), body


def theta(scope=0):
    matrix = [I(1, 0, 0), I(1, 0, 0)]
    return ['intro', matrix, refl(I(S(-scope - 1), 0, 0))]


def name_matrix(t):
    return [I(1, 0, 3), I(1, 0, t)]


def name_compound_zero():
    t, z = I(0, 0, 0), -1
    matrix = name_matrix(t)
    body = K.sub(matrix, 0, 2)
    clauses = ((K.H, K.sub(body, z)),)
    left = succ(z, 0, 0)
    right = trans(succ(z, 0, t), zero(), clauses, 1)
    branch = join(left, right, clauses, 1)
    return ['intro', matrix, branch]


def progress_example():
    matrix = [I(1, 0, I(0, 1, 0)), I(1, 0, 1)]
    z = -1
    lo, ro = I(z, 0, I(0, 1, 0)), I(z, 0, 1)
    clauses = ((K.H, [lo, ro]),)
    left = trans(succ(z, 0, I(0, 1, 0)), zero(lo), clauses, 1)
    p = trans(left, use(0), clauses, 1)
    p = trans(p, sym(succ(z, 0, 1), clauses, 1), clauses, 1)
    return ['intro', matrix, p]


def coverage(r):
    """A(r) = D_(x,v) [ C(v,0,C(r,0,Sx)) = C(v,0,r) ]."""
    r = K.shift(r, 2)
    return [[C(1, 0, C(r, 0, S(2))), C(1, 0, r)]]


def coverage_closure():
    # Outer witness is unused. Its successor parameter z becomes the newest
    # witness for the inner introduction. The inner proof uses computations.
    outer_matrix = coverage(1)
    z, w = -1, -2
    inner_matrix = coverage(S(z))[0]
    outer_body = K.sub(outer_matrix, 0, 2)
    outer_clause = (K.H, K.sub(outer_body, 0))
    inner_body = K.sub(inner_matrix, z, 2)
    clauses = (outer_clause, (K.H, K.sub(inner_body, w)))
    left = trans(succ(w, 0, C(S(z), 0, S(z))),
                 succ(z, 0, S(z)), clauses, 2)
    right = succ(w, 0, S(z))
    inner = ['intro', inner_matrix, join(left, right, clauses, 2)]
    return ['intro', outer_matrix, inner]


def coverage_zero(clauses, scope):
    matrix = coverage(0)[0]
    x, z = -scope, -scope - 1
    body = K.sub(matrix, x, 2)
    local = clauses + ((K.H, K.sub(body, z)),)
    left = trans(succ(z, 0, C(0, 0, S(x))),
                 zero(0, S(x)), local, scope + 1)
    right = succ(z, 0, 0)
    return ['intro', matrix, join(left, right, local, scope + 1)]


def specialized_coverage(t):
    # Open the unused witness of Q_r A(r), instantiate at S(t), and export
    # A(S(t)); no predecessor theorem or equality reflection is used.
    outer = coverage_closure()
    clause = opened(result(outer)[0], -1)
    base = coverage_zero((clause,), 1)
    return ['open', outer, use(0, S(t), base)]


def extracted_successor_equality(t):
    # Open the instantiated packet, prove its zero row, specialize at one,
    # and expose S(b)=S(t) by explicit computation equations and transport.
    # The concluding constant transport checks this equality before exporting
    # the closed equation 0=0 through both existential discharges.
    outer = coverage_closure()
    clause0 = opened(result(outer)[0], -1)
    base0 = coverage_zero((clause0,), 1)
    major = use(0, S(t), base0)
    matrix = coverage(S(t))[0]
    b = -2
    clause1 = opened(matrix, b)
    local = (clause0, clause1)
    seed = join(zero(0, C(S(t), 0, S(b))), zero(0, S(t)), local, 2)
    row = use(1, S(0), seed)
    left = trans(succ(0, 0, C(S(t), 0, S(b))),
                 succ(t, 0, S(b)), local, 2)
    right = succ(0, 0, S(t))
    eq = trans(trans(sym(left, local, 2), row, local, 2), right, local, 2)
    if result(eq, local, 2) != [S(b), S(t)]:
        raise ValueError('wrong extracted successor equation')
    finish = tr([0, 0], eq, refl(0))
    return ['open', outer, ['open', major, finish]]


def newest_parameter_examples():
    matrix = name_matrix(-1)
    first = ['intro', matrix, refl(I(S(-2), 0, -1))]
    positive = ['open', theta(), ['open', first, refl(0)]]
    # Adjust the genuinely fresh successor parameter, but keep the old
    # witness -1. The new newest parameter is -2, so this replay is invalid.
    replay = ['intro', matrix, refl(I(S(-3), 0, -1))]
    negative = ['open', theta(), ['open', theta(1), ['open', replay, refl(0)]]]
    return positive, negative


def make_cases():
    t = I(S(S(0)), S(0), S(1))
    newest, failed_replay = newest_parameter_examples()
    proofs = {
        'zero_computation': zero(S(0), S(1)),
        'successor_computation': succ(S(0), 0, S(1)),
        'reflexivity_nested_iterator': refl(t),
        'unused_witness_neutral': theta(),
        'compound_zero_naming_new_policy': name_compound_zero(),
        'progress_uses_induction_hypothesis': progress_example(),
        'compound_case_uses_base': ['intro', [name_matrix(0)], use(0)],
        'universal_coverage_closure': coverage_closure(),
        'coverage_at_successor_of_compound': specialized_coverage(t),
        'extract_successor_equality_then_discharge': extracted_successor_equality(t),
        'newest_parameter_after_open': newest,
    }
    accepted = {name: {'goal': result(p), 'proof': p} for name, p in proofs.items()}
    rejected = {'naive_weakening_changes_selected_witness': {'goal': [0, 0], 'proof': failed_replay}}
    rejected['false_goal'] = {'goal': [0, S(0)], 'proof': refl(0)}
    rejected['escaped_parameter'] = {'goal': [-1, -1], 'proof': refl(-1)}
    rejected['unbound_goal'] = {'goal': [1, 1], 'proof': refl(1)}
    rejected['boolean_goal'] = {'goal': [False, False], 'proof': refl(False)}
    rejected['float_goal'] = {'goal': [0.0, 0.0], 'proof': refl(0.0)}
    rejected['unguarded_atomic_matrix'] = {'goal': [[0, 0]], 'proof': ['intro', [0, 0], refl(0)]}
    rejected['out_of_scope_transport_template'] = {'goal': [0, 0], 'proof': tr([2, 2], refl(0), refl(0))}
    rejected['unavailable_clause'] = {'goal': [0, 0], 'proof': use(0)}
    rejected['boolean_clause_index'] = {'goal': [0, 0], 'proof': ['open', theta(), use(False)]}
    rejected['witness_escapes_discharge'] = {'goal': [0, 0], 'proof': ['open', theta(), refl(-1)]}
    rejected['obsolete_witness_field'] = {'goal': accepted['unused_witness_neutral']['goal'], 'proof': ['intro', result(theta())[0], 0, refl(0)]}
    rejected['wrong_zero_packet_arity'] = {'goal': [0, 0], 'proof': ['zero', 0]}
    rejected['term_as_formula'] = {'goal': I(0, 0, 0), 'proof': refl(0)}
    rejected['forged_computation_body_scope'] = {'goal': [0, 0], 'proof': ['zero', 0, 2]}
    rejected['unknown_instruction'] = {'goal': [0, 0], 'proof': ['accept']}
    rejected['extra_top_level_key'] = dict(accepted['zero_computation'], extra=0)
    return accepted, rejected


def elaborate(proof, clauses=(), scope=0):
    """Insert the selected witness into the old unrestricted certificate."""
    tag = proof[0]
    if tag in ('zero', 'succ'):
        return copy.deepcopy(proof)
    if tag == 'use':
        return [tag, proof[1], proof[2], elaborate(proof[3], clauses, scope)]
    if tag == 'tr':
        return [tag, proof[1], elaborate(proof[2], clauses, scope),
                elaborate(proof[3], clauses, scope)]
    if tag == 'open':
        matrix = result(proof[1], clauses, scope)[0]
        local = clauses + (opened(matrix, -scope - 1),)
        return [tag, elaborate(proof[1], clauses, scope),
                elaborate(proof[2], local, scope + 1)]
    if tag == 'intro':
        matrix, branch = proof[1:]
        witness, fresh = -scope, -scope - 1
        body = K.sub(matrix, witness, 2)
        base = K.sub(body, fresh if len(matrix) == 2 else 0)
        local = clauses + ((K.H, base),)
        return [tag, matrix, witness, elaborate(branch, local, scope + 1)]
    raise ValueError('unknown instruction')


def measure(path):
    tree = ast.parse(path.read_bytes())
    if tree.body and isinstance(tree.body[0], ast.Expr) and isinstance(tree.body[0].value, ast.Constant) and isinstance(tree.body[0].value.value, str):
        tree.body.pop(0)
    normalized = ast.unparse(tree) + '\n'
    ignored = {getattr(tokenize, n) for n in ('ENCODING', 'ENDMARKER', 'COMMENT', 'NL', 'NEWLINE', 'INDENT', 'DEDENT')}
    return {
        'file': path.name,
        'normalized_bytes': len(normalized.encode()),
        'tokens': sum(t.type not in ignored for t in tokenize.generate_tokens(io.StringIO(normalized).readline)),
        'ast_nodes': len(list(ast.walk(tree))),
        'gzip9': len(gzip.compress(normalized.encode(), compresslevel=9, mtime=0)),
        'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
    }


def patch_audit():
    old = (ROOT / 'control_naming_exception.py').read_text()
    start, end = old.index('\ndef witness('), old.index('\n\nH =')
    expected = old[:start] + old[end:]
    expected = expected.replace('t = witness(matrix, scope)', 't = -scope')
    old_ast, new_ast = ast.parse(expected), ast.parse((ROOT / 'checker.py').read_text())
    old_ast.body.pop(0)
    new_ast.body.pop(0)
    if ast.dump(old_ast) != ast.dump(new_ast):
        raise ValueError('undeclared checker change')
    return {'exact_ast_patch': True, 'deleted_helper': 'witness', 'new_selector': '-scope'}


def cli(program, payload, optimized=False):
    p = subprocess.run([sys.executable] + (['-O'] if optimized else []) + [str(ROOT / program)],
                       input=json.dumps(payload), text=True, capture_output=True, timeout=30)
    return p.returncode == 0 and p.stdout == 'ACCEPT\n'


def main():
    accepted, rejected = make_cases()
    runs = []
    for label, cases, expected in [('accepted', accepted, True), ('rejected', rejected, False)]:
        folder = ROOT / 'examples' / label
        folder.mkdir(parents=True, exist_ok=True)
        for name, data in cases.items():
            (folder / (name + '.json')).write_text(json.dumps(data, separators=(',', ':')) + '\n')
            for optimized in (False, True):
                actual = cli('checker.py', data, optimized)
                if actual != expected:
                    raise AssertionError((name, optimized, expected, actual))
                runs.append({'case': name, 'optimized': optimized, 'expected': expected, 'accepted': actual})
    distinguishing = accepted['compound_zero_naming_new_policy']
    if cli('control_naming_exception.py', distinguishing):
        raise AssertionError('the old selector should reject the tailored new branch')
    scoped_major = coverage_closure()
    if result(scoped_major) != [coverage(1)]:
        raise AssertionError('wrong universal closure')
    elaborated_dir = ROOT / 'examples' / 'elaborated_unrestricted'
    elaborated_dir.mkdir(parents=True, exist_ok=True)
    for name, data in accepted.items():
        source = {'goal': data['goal'], 'proof': elaborate(data['proof'])}
        UNRESTRICTED.check(source)
        (elaborated_dir / (name + '.json')).write_text(json.dumps(source, separators=(',', ':')) + '\n')
    metrics = [measure(ROOT / p) for p in ('control_naming_exception.py', 'checker.py')]
    report = {'python': sys.version, 'patch': patch_audit(), 'accepted_certificates': len(accepted),
              'rejected_certificates': len(rejected), 'cli_runs': len(runs), 'normal_and_optimized': True,
              'old_selector_rejects_new_tailored_branch': True,
              'unrestricted_elaboration_replays': len(accepted),
              'universal_coverage_and_successor_equality_extraction': True,
              'general_predecessor_certificate_supplied': False,
              'formal_verification': False, 'metrics': metrics, 'runs': runs}
    (ROOT / 'metrics.json').write_text(json.dumps(metrics, indent=2) + '\n')
    (ROOT / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'runs'}, indent=2))


if __name__ == '__main__':
    main()

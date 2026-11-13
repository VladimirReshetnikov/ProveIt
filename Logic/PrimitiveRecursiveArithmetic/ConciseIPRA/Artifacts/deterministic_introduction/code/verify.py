"""Untrusted certificate builders, matched comparisons and finite regressions."""
import ast
import copy
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

import checker as K
import control as C

ROOT = Path(__file__).resolve().parent


def S(t):
    return [0, t]


def I(n, a, h):
    return [n, a, h]


def zero(a=0, h=0):
    return ['zero', a, h]


def succ(n, a, h):
    return ['succ', n, a, h]


def refl(t):
    p = zero(t)
    return ['tr', [1, t], p, p]


def tr(template, p, q):
    return ['tr', template, p, q]


def result(p, clauses=(), scope=0, kernel=K):
    return kernel.infer(p, clauses, scope)


def sym(p, clauses=(), scope=0):
    s, t = result(p, clauses, scope)
    return tr([1, s], p, refl(s))


def trans(p, q, clauses=(), scope=0):
    s, t = result(p, clauses, scope)
    u, v = result(q, clauses, scope)
    assert t == u
    return tr([s, 1], q, p)


def use(j, t=0, p=None):
    return ['use', j, t, zero() if p is None else p]


def name_matrix(t):
    return [I(1, 0, 3), I(1, 0, t)]


def named(t, scope=0):
    z = -scope - 1
    return ['intro', name_matrix(t), refl(I(S(z), 0, t))]


def opened_clause(matrix, b):
    body = K.sub(matrix, b, 2)
    return (K.sub(body, 0), body)


def naming_equality(t, b, index, clauses, scope):
    p0 = zero(0, b)
    q0 = zero(0, t)
    base = trans(p0, sym(q0, clauses, scope), clauses, scope)
    row = use(index, S(0), base)
    left = succ(0, 0, b)
    right = succ(0, 0, t)
    p = tr([1, I(S(0), 0, t)], left, row)
    return tr([b, 1], right, p)


def deterministic_to_control(proof, clauses=(), scope=0):
    tag = proof[0]
    if tag in ('zero', 'succ'):
        return copy.deepcopy(proof)
    if tag == 'use':
        return [tag, proof[1], proof[2], deterministic_to_control(proof[3], clauses, scope)]
    if tag == 'tr':
        return [tag, proof[1], deterministic_to_control(proof[2], clauses, scope), deterministic_to_control(proof[3], clauses, scope)]
    if tag == 'open':
        matrix = K.infer(proof[1], clauses, scope)[0]
        new = clauses + (opened_clause(matrix, -scope - 1),)
        return [tag, deterministic_to_control(proof[1], clauses, scope), deterministic_to_control(proof[2], new, scope + 1)]
    if tag == 'intro':
        matrix = proof[1]
        t = K.witness(matrix, scope)
        body = K.sub(matrix, t, 2)
        base = K.sub(body, -scope - 1 if len(matrix) == 2 else 0)
        p = deterministic_to_control(proof[2], clauses + ((K.H, base),), scope + 1)
        return [tag, matrix, t, p]
    raise ValueError(tag)


def progress_example():
    # I(y,0;u.I(0,u;v.0)) = I(y,0;u.u).
    # The branch genuinely uses its equation induction hypothesis.
    matrix = [I(1, 0, I(0, 1, 0)), I(1, 0, 1)]
    z = -1
    lo, ro = I(z, 0, I(0, 1, 0)), I(z, 0, 1)
    clauses = ((K.H, [lo, ro]),)
    left = trans(succ(z, 0, I(0, 1, 0)), zero(lo), clauses, 1)
    p = trans(left, use(0), clauses, 1)
    p = trans(p, sym(succ(z, 0, 1), clauses, 1), clauses, 1)
    return ['intro', matrix, p]


def arbitrary_witness_example(t):
    # D(x,y): C(y,0,Sx) = C(y,0,St), not a naming matrix.
    matrix = [I(1, 0, S(3)), I(1, 0, S(t))]
    old_branch = refl(I(S(-1), 0, S(t)))
    old = ['intro', matrix, t, old_branch]
    b, z = -1, -2
    name_clause = opened_clause(name_matrix(t), b)
    body = K.sub(matrix, b, 2)
    branch_assumption = K.sub(body, z)
    clauses = (name_clause, (K.H, branch_assumption))
    eq = naming_equality(t, b, 0, clauses, 2)
    reverse = sym(eq, clauses, 2)
    old_successor = refl(I(S(z), 0, S(t)))
    template = [I(S(z), 0, S(2)), I(S(z), 0, S(t))]
    # The template variable is below the iterator's state binder, hence 2.
    repaired = tr(template, reverse, old_successor)
    new = ['open', named(t), ['intro', matrix, repaired]]
    assert C.infer(old) == K.infer(new)
    return old, new


def use_old_parameter_after_newer_scope():
    # A real occurrence of the weakening repair: after naming a=2 and
    # opening an unrelated newer parameter c=0, name a once more as e=a.
    # The final non-naming introduction then uses newest e, and the proof
    # transports only through computations, Use and Tr.
    target = S(S(0))
    a, c, e, z = -1, -2, -3, -4
    major_a = named(target)
    clause_a = opened_clause(name_matrix(target), a)
    major_c = named(0, 1)
    clause_c = opened_clause(name_matrix(0), c)
    major_e = named(a, 2)
    clause_e = opened_clause(name_matrix(a), e)
    matrix = [I(1, 0, S(3)), I(1, 0, S(target))]
    body = K.sub(matrix, e, 2)
    clauses = (clause_a, clause_c, clause_e, (K.H, K.sub(body, z)))
    ea = naming_equality(a, e, 2, clauses, 4)
    at = naming_equality(target, a, 0, clauses, 4)
    et = trans(ea, at, clauses, 4)
    te = sym(et, clauses, 4)
    template = [I(S(z), 0, S(2)), I(S(z), 0, S(target))]
    branch = tr(template, te, refl(I(S(z), 0, S(target))))
    return ['open', major_a, ['open', major_c, ['open', major_e, ['intro', matrix, branch]]]]


def weakening_original_and_failed_replay():
    target, a = S(S(0)), -1
    matrix = [I(1, 0, S(3)), I(1, 0, S(target))]
    clause_a = opened_clause(name_matrix(target), a)

    def old_intro(scope, outer_clauses):
        z = -scope - 1
        body = K.sub(matrix, -scope, 2)
        clauses = outer_clauses + ((K.H, K.sub(body, z)),)
        at = naming_equality(target, a, 0, clauses, scope + 1)
        ta = sym(at, clauses, scope + 1)
        template = [I(S(z), 0, S(2)), I(S(z), 0, S(target))]
        branch = tr(template, ta, refl(I(S(z), 0, S(target))))
        return ['intro', matrix, branch]

    original = ['open', named(target), old_intro(1, (clause_a,))]
    clause_c = opened_clause(name_matrix(0), -2)
    failed = ['open', named(target), ['open', named(0, 1), old_intro(2, (clause_a, clause_c))]]
    return original, failed


def make_examples():
    t = I(S(S(0)), S(0), S(1))
    old, translated = arbitrary_witness_example(t)
    compound = [name_matrix(0)]
    weakening_original, weakening_failed = weakening_original_and_failed_replay()
    positives = {
        'reflexivity_zero': refl(0),
        'reflexivity_nested_iterator': refl(t),
        'name_zero': named(0),
        'name_numeral': named(S(S(0))),
        'name_compound_iterator': named(t),
        'progress_uses_hypothesis': progress_example(),
        'compound_case_uses_base': ['intro', compound, use(0)],
        'arbitrary_witness_translated': translated,
        'old_parameter_after_newer_scope': use_old_parameter_after_newer_scope(),
        'old_parameter_before_scope_extension': weakening_original,
    }
    accepted = {name: {'goal': K.infer(p), 'proof': p} for name, p in positives.items()}
    controls = {name: {'goal': data['goal'], 'proof': deterministic_to_control(data['proof'])} for name, data in accepted.items()}
    controls['original_arbitrary_witness'] = {'goal': C.infer(old), 'proof': old}
    invalid = {}
    invalid['naive_scope_weakening_changes_witness'] = {'goal': K.infer(weakening_original), 'proof': weakening_failed}
    p = copy.deepcopy(accepted['name_zero'])
    p['goal'] = [0, S(0)]
    invalid['false_goal'] = p
    p = copy.deepcopy(accepted['name_zero'])
    p['proof'].insert(2, 0)
    invalid['obsolete_witness_field'] = p
    p = copy.deepcopy(accepted['name_compound_iterator'])
    p['proof'][1][1][2] = -1
    invalid['future_parameter_in_name'] = p
    p = copy.deepcopy(accepted['name_zero'])
    p['proof'][1][0][1] = S(0)
    invalid['unguarded_atomic_matrix'] = p
    for name, bad_target in [('witness', S(3)), ('row', S(2)), ('state', S(1))]:
        matrix = [I(1, 0, 3), I(1, 0, bad_target)]
        assert K.formula([matrix], 0)
        assert K.witness(matrix, 0) == 0
        invalid['naming_target_uses_' + name] = {'goal': [matrix], 'proof': ['intro', matrix, refl(I(S(-1), 0, 0))]}
    invalid['witness_escapes_open'] = {'goal': [0, 0], 'proof': ['open', named(0), refl(-1)]}
    invalid['free_goal'] = {'goal': [-1, -1], 'proof': refl(-1)}
    invalid['unbound_goal'] = {'goal': [1, 1], 'proof': refl(1)}
    invalid['boolean_term'] = {'goal': [False, False], 'proof': refl(False)}
    invalid['missing_clause'] = {'goal': [0, 0], 'proof': use(0)}
    invalid['wrong_use_antecedent'] = {'goal': [[name_matrix(0)]], 'proof': ['intro', [name_matrix(0)], use(0, 0, refl(0))]}
    invalid['bad_transport_major'] = {'goal': [0, 0], 'proof': tr([1, 1], named(0), refl(0))}
    invalid['bad_transport_template'] = {'goal': [0, 0], 'proof': tr([2, 2], refl(0), refl(0))}
    invalid['wrong_packet_arity'] = {'goal': [0, 0], 'proof': ['zero', 0]}
    invalid['extra_input_key'] = dict(accepted['name_zero'], extra=True)
    return accepted, controls, invalid


def metrics(path):
    tree = ast.parse(path.read_text())
    if tree.body and isinstance(tree.body[0], ast.Expr) and isinstance(tree.body[0].value, ast.Constant) and isinstance(tree.body[0].value.value, str):
        tree.body.pop(0)
    source = ast.unparse(tree) + '\n'
    counted = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    tokens = sum(token.type not in counted for token in tokenize.generate_tokens(io.StringIO(source).readline))
    return {'normalized_bytes': len(source.encode()), 'significant_tokens': tokens, 'ast_nodes': sum(1 for _ in ast.walk(ast.parse(source))), 'gzip9': len(gzip.compress(source.encode(), compresslevel=9, mtime=0)), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def main():
    accepted, controls, invalid = make_examples()
    runs = []
    for folder, cases in [('accepted', accepted), ('control', controls), ('rejected', invalid)]:
        directory = ROOT / 'examples' / folder
        directory.mkdir(parents=True, exist_ok=True)
        for name, data in cases.items():
            path = directory / (name + '.json')
            path.write_text(json.dumps(data, separators=(',', ':')) + '\n')
            program = 'control.py' if folder == 'control' else 'checker.py'
            expected = folder != 'rejected'
            for optimized in [False, True]:
                command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT / program)]
                r = subprocess.run(command, input=json.dumps(data), text=True, capture_output=True)
                actual = r.returncode == 0 and r.stdout.strip() == 'ACCEPT'
                if actual != expected:
                    raise AssertionError((folder, name, optimized, r.returncode, r.stdout, r.stderr))
                runs.append({'case': name, 'program': program, 'optimized': optimized, 'expected_accept': expected, 'accepted': actual})
    # Binder regressions independently stated as exact mathematical instances.
    assert K.sub([1, 2], S(0)) == [S(0), 1]
    assert K.sub([[1, 0, 3], [1, 0, -1]], -2, 2) == [[1, 0, -2], [1, 0, -1]]
    assert K.sub([0, 0, 2], 1) == [0, 0, 2]
    assert K.shift([[3, 3]], 1) == [[4, 4]]
    assert K.sub([[3, 3]], S(0)) == [[S(0), S(0)]]
    measurements = {p: metrics(ROOT / p) for p in ['checker.py', 'control.py']}
    report = {'python': sys.version, 'accepted': len(accepted), 'control_certificates': len(controls), 'rejected': len(invalid), 'cli_runs': len(runs), 'binding_regressions': 5, 'exact_embedding_checks': len(accepted), 'arbitrary_witness_translation_pairs': 1, 'newest_parameter_repair_examples': 1, 'measurements': measurements, 'runs': runs, 'formal_verification': False}
    (ROOT / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'runs'}, indent=2))


if __name__ == '__main__':
    main()

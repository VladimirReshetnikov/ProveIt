"""Focused checks for the alternative full-language mirror dispatch.

The checker is the diagonal clausal checker with only its guard replaced.
This script is an untrusted proof producer and test runner.
"""
import ast
import copy
import gzip
import io
import json
from pathlib import Path
import random
import subprocess
import sys
import tokenize
import checker as C
import proof_tools as P


ROOT = Path(__file__).resolve().parent
EXAMPLES = ROOT / 'examples'
EXAMPLES.mkdir(exist_ok=True)


def rejects(proof, context=(), scope=0):
    try:
        C.derive(proof, list(context), scope)
    except Exception:
        return True
    return False


def cut_ordinary(proof, index, theorem):
    """Replace uses of one ordinary-assumption clause by an independent proof.

    The context slot is kept, so other indices need not change. The supplied
    theorem must be independent of this slot. Its free levels remain fixed
    when the surrounding derivation enters further eigenparameter scopes.
    """
    tag = proof[0]
    if tag == 'u':
        if proof[1] == index:
            return copy.deepcopy(theorem)
        return ['u', proof[1], copy.deepcopy(proof[2]),
                cut_ordinary(proof[3], index, theorem)]
    if tag == 'r':
        return copy.deepcopy(proof)
    if tag == 'v':
        return ['v', cut_ordinary(proof[1], index, theorem),
                cut_ordinary(proof[2], index, theorem)]
    if tag == 'e':
        return ['e', copy.deepcopy(proof[1]),
                cut_ordinary(proof[2], index, theorem),
                cut_ordinary(proof[3], index, theorem)]
    if tag == 'i':
        return ['i', copy.deepcopy(proof[1]), copy.deepcopy(proof[2]),
                cut_ordinary(proof[3], index, theorem)]
    raise ValueError('invalid proof tag')


def closed_certificate(proof):
    data = {'goal': P.value(proof), 'proof': proof}
    assert C.verify(data)
    return data


positive = {}
positive['reflexivity'] = closed_certificate(P.refl(0))
positive['zero_computation'] = closed_certificate(P.zero(P.S(0), P.S(1)))
positive['successor_computation'] = closed_certificate(P.successor(P.S(0), 0, P.S(1)))
positive['symmetry'] = closed_certificate(P.sym(P.zero(P.S(0), 1)))
positive['nested_template_congruence'] = closed_certificate(P.congr(
    P.I(1, P.S(1), P.I(2, 1, P.S(1))), P.zero(0, 1)))

# H(y) is y = I(y,y;u.y), a mirror matrix. The branch actually invokes H(z),
# although the theorem also has a shorter proof that ignores that hypothesis.
mirror_goal = [[1, P.I(1, 1, 2)]]
assert C.diagonal(mirror_goal[0])
mirror_ctx, mirror_target = P.intro_context(mirror_goal, 0, [], 0)
fresh = -1
reflexive_endpoint = P.congr(mirror_target[0], P.use(0), mirror_ctx, 1)
computed_endpoint = P.sym(P.successor(fresh, P.S(fresh), P.S(fresh)),
                          mirror_ctx, 1)
mirror_branch = P.trans(reflexive_endpoint, computed_endpoint, mirror_ctx, 1)
positive['mirror_progress_uses_hypothesis'] = closed_certificate(
    ['i', mirror_goal, 0, mirror_branch])
positive['mirror_nonzero_witness'] = closed_certificate(
    ['i', mirror_goal, P.S(0), mirror_branch])

# B(x,y) := p = I(y,q;u.q). It is unguarded when p and q are different free
# parameters. Its case premise requires its local zero base: convert that
# base to p=q, then expand q to the successor iterator.
open_goal = [[-1, P.I(1, -2, -2)]]
assert not C.diagonal(open_goal[0])
case_ctx, case_target = P.intro_context(open_goal, 0, [], 2)
case_branch = P.trans(
    P.trans(P.use(0), P.zero(-2, -2), case_ctx, 3),
    P.sym(P.successor(-3, -2, -2), case_ctx, 3), case_ctx, 3)
open_proof = ['i', open_goal, 0, case_branch]
assert C.derive(open_proof, [], 2) == open_goal

created_guards = []
created_guard_negatives = {}
for name, image, new_scope in [
    ('zero', 0, 0),
    ('successor', P.S(0), 0),
    ('nested_iterator', P.I(P.S(0), 0, P.S(1)), 0),
    ('open_parameter', -1, 1),
    ('open_composite', P.I(-1, P.S(-2), P.S(1)), 2),
]:
    mapping = {-1: image, -2: image}
    naive = P.substitute(open_proof, mapping, 2, new_scope)
    image_goal = P.substitute(open_goal, mapping, 2, new_scope)
    assert C.diagonal(image_goal[0])
    # Direct tree substitution does NOT work: its branch expects B(0), but
    # the new primitive rule assumes B(z). This negative check matters.
    assert rejects(naive, [], new_scope), name
    context, target = P.intro_context(image_goal, 0, [], new_scope)
    zero_base = P.sym(P.zero(image, image), context, new_scope + 1)
    repaired = copy.deepcopy(naive)
    repaired[3] = cut_ordinary(naive[3], 0, zero_base)
    assert C.derive(repaired, [], new_scope) == image_goal, name
    assert C.derive(repaired[3], context, new_scope + 1) == target
    if new_scope == 0:
        positive['created_guard_repaired_' + name] = closed_certificate(repaired)
        created_guard_negatives['created_guard_naive_' + name] = {
            'goal': image_goal, 'proof': naive}
    created_guards.append({'name': name, 'scope': new_scope,
                           'naive_rejected': True, 'repair_accepted': True})

# If the two free parameters remain syntactically distinct, the case mode
# is preserved and the direct proof image is accepted.
unchanged_case = P.substitute(open_proof, {-1: 0, -2: P.S(0)}, 2, 0)
assert not C.diagonal(unchanged_case[1][0])
positive['unguarded_case_substitution'] = closed_certificate(unchanged_case)

# A guarded open matrix stays guarded. Cases that merely prove its two sides
# equal but do not identify their syntax do not create the guard.
syntactically_distinct = P.substitute(open_proof,
                                     {-1: 0, -2: P.I(0, 0, 0)}, 2, 0)
assert not C.diagonal(syntactically_distinct[1][0])
positive['equal_values_do_not_create_guard'] = closed_certificate(syntactically_distinct)

# A D elimination uses the released conditional clause and a checked base.
paired = positive['mirror_progress_uses_hypothesis']['proof']
body = C.opening(mirror_goal[0], -1, 1)
elim_ctx = [(C.opening(body, 0), body)]
base = P.sym(P.zero(0, 0), elim_ctx, 1)
used = P.use(0, P.S(0), base)
elim_branch = P.congr(0, used, elim_ctx, 1)
positive['elimination_used_clause'] = closed_certificate(
    ['e', [0, 0], paired, elim_branch])

negative = dict(created_guard_negatives)
negative['wrong_goal'] = {'goal': [0, P.S(0)], 'proof': P.refl(0)}
negative['eigenvariable_escape'] = {'goal': [-1, -1], 'proof': P.refl(-1)}
negative['unbound_index'] = {'goal': [1, 1], 'proof': P.refl(1)}
negative['boolean_term'] = {'goal': [False, False], 'proof': P.refl(False)}
negative['float_term'] = {'goal': [0.0, 0.0], 'proof': P.refl(0.0)}
negative['invalid_successor'] = {'goal': [[1, 0], [1, 0]], 'proof': P.refl([1, 0])}
negative['empty_term'] = {'goal': [[], []], 'proof': P.refl([])}
negative['unbound_witness'] = {'goal': [[0, 0]],
                             'proof': ['i', [[0, 0]], -1, P.refl(0)]}
negative['incorrect_eval_source'] = {
    'goal': [0, 0],
    'proof': ['v', P.refl(0), P.refl(P.I(P.S(0), P.S(0), 1))]}
bad_base = copy.deepcopy(positive['elimination_used_clause'])
bad_base['proof'][3] = P.use(0, 0, P.refl(0))
negative['wrong_clause_base'] = bad_base

for name, data in positive.items():
    assert C.verify(data)
    (EXAMPLES / (name + '.json')).write_text(json.dumps(data, separators=(',', ':')) + '\n')
for name, data in negative.items():
    try:
        C.verify(data)
    except Exception:
        pass
    else:
        raise AssertionError(name)
    (EXAMPLES / ('reject_' + name + '.json')).write_text(
        json.dumps(data, separators=(',', ':')) + '\n')

# Random checks of the direction that is actually true. The converse is
# deliberately not asserted; the created-guard examples refute it.
rng = random.Random(941278)


def random_term(scope, depth, fuel):
    if fuel == 0 or rng.random() < 0.45:
        return rng.randint(-scope, depth)
    if rng.random() < 0.4:
        return P.S(random_term(scope, depth, fuel - 1))
    return P.I(random_term(scope, depth, fuel - 1),
               random_term(scope, depth, fuel - 1),
               random_term(scope, depth + 1, fuel - 1))


for _ in range(300):
    scope = rng.randrange(1, 4)
    new_scope = rng.randrange(0, 4)
    left = random_term(scope, 2, 3)
    matrix = [left, P.I(1, left, random_term(scope, 3, 3))]
    mapping = {-i: random_term(new_scope, 0, 2)
               for i in range(1, scope + 1)}
    image = P.substitute(matrix, mapping, scope, new_scope)
    assert C.formula(matrix, scope, 2) and C.formula(image, new_scope, 2)
    assert C.diagonal(matrix) and C.diagonal(image)

process_checks = 0
for mode in ([], ['-O']):
    for expected, table in [(True, positive), (False, negative)]:
        for name, data in table.items():
            p = subprocess.run([sys.executable] + mode + [str(ROOT / 'checker.py')],
                               input=json.dumps(data), text=True, capture_output=True)
            assert ((p.returncode == 0 and p.stdout == 'ACCEPT\n') if expected
                    else (p.returncode != 0 and p.stdout == 'REJECT\n')), (name, p)
            process_checks += 1

skip = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.COMMENT,
        tokenize.NL, tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT}
metrics = {}
sources = {
    'mirror_clausal': ROOT / 'checker.py',
    'diagonal_clausal': ROOT.parent / 'diagonal/checker.py',
    'diagonal_native': ROOT.parent / 'diagonal/native_diagonal_control.py',
    'witness_clausal': ROOT.parent / 'diagonal/witness_control.py',
}
for name, path in sources.items():
    if not path.exists():
        continue
    tree = ast.parse(path.read_text())
    if isinstance(tree.body[0], ast.Expr) and isinstance(tree.body[0].value, ast.Constant):
        del tree.body[0]
    source = ast.unparse(tree) + '\n'
    metrics[name] = {
        'bytes': len(source.encode()),
        'tokens': sum(t.type not in skip for t in tokenize.generate_tokens(io.StringIO(source).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(tree)),
        'gzip_9_bytes': len(gzip.compress(source.encode(), compresslevel=9, mtime=0)),
    }
    if name == 'mirror_clausal':
        (ROOT / 'checker.normalized.py').write_text(source)

result = {'status': 'all checks passed', 'positive': list(positive),
          'negative': list(negative), 'created_guard_substitutions': created_guards,
          'guard_preservation_cases': 300, 'process_checks': process_checks,
          'metrics': metrics, 'python': sys.version}
(ROOT / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))

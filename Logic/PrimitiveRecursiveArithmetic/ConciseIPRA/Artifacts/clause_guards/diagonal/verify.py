"""Reproduce finite implementation checks, exact translations and sizes."""
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
import native_diagonal_control as N
import witness_control as W
import proof_tools as P

ROOT = Path(__file__).resolve().parent
EXAMPLES = ROOT / 'examples'
EXAMPLES.mkdir(exist_ok=True)


def cert(p):
    return {'goal': P.value(p), 'proof': p}


def expected_reject(data, engine=C):
    try:
        engine.verify(data)
    except Exception:
        return True
    return False


positive = {}
positive['reflexivity'] = cert(P.refl(0))
positive['zero_computation'] = cert(P.zero(P.S(0), P.S(1)))
positive['successor_computation'] = cert(P.successor(P.S(0), 0, P.S(1)))
positive['symmetry'] = cert(P.sym(P.zero(P.S(0), 1)))
positive['root_pivot'] = cert(P.pivot(P.zero(0, 1), P.zero(0, 1)))
positive['nested_template_congruence'] = cert(P.congr(P.I(1, P.S(1), P.I(2, 1, P.S(1))), P.zero(0, 1)))

# Diagonal progress uses the actual retained hypothesis in a constant context.
# The theorem is reflexive, but its proof would fail if the branch hypothesis
# were silently changed from B(t,z) to B(t,0).
diag_goal = [[P.I(1, 1, P.S(1)), P.I(1, 1, P.S(1))]]
diag_ctx, diag_target = P.intro_context(diag_goal, 0, [], 0)
diag_branch = P.congr(diag_target[0], P.use(0), diag_ctx, 1)
positive['diagonal_progress_uses_hypothesis'] = cert(['i', diag_goal, 0, diag_branch])
positive['diagonal_nonzero_witness'] = cert(['i', diag_goal, P.S(0), diag_branch])

# Non-diagonal case introduction has an update mentioning the numerical y
# under the iterator state binder; this exercises nested capture-safe opening.
case_goal = [[P.I(0, 2, 2), 2]]
case_proof = ['i', case_goal, P.S(0), P.zero(P.S(0), P.S(-1))]
positive['case_capture_control'] = cert(case_proof)

# A D elimination actually uses its canonical clause and its required base.
fresh = -1
paired = positive['case_capture_control']['proof']
body = C.opening(case_goal[0], fresh, 1)
elim_ctx = [(C.opening(body, 0), body)]
clause_use = P.use(0, P.S(0), P.zero(fresh, 0))
elim_branch = P.congr(0, clause_use, elim_ctx, 1)
positive['elimination_used_clause'] = cert(['e', [0, 0], paired, elim_branch])

# Nested logical binders retain protected indices while opening the outer x.
nested_goal = [[[4, 4]]]
nested_proof = ['i', nested_goal, 0, ['i', [[0, 0]], 0, P.refl(0)]]
positive['nested_d'] = cert(nested_proof)

# A canonical clause can be specialized more than once in the same branch.
use0 = P.use(0, 0, P.zero(fresh, 0))
use1 = P.use(0, P.S(0), P.zero(fresh, 0))
repeat_branch = P.trans(P.congr(0, use0, elim_ctx, 1),
                        P.congr(0, use1, elim_ctx, 1), elim_ctx, 1)
positive['clause_reuse'] = cert(['e', [0, 0], paired, repeat_branch])

negative = {}
negative['wrong_goal'] = {'goal': [0, P.S(0)], 'proof': P.refl(0)}
negative['eigenvariable_escape'] = {'goal': [-1, -1], 'proof': P.refl(-1)}
negative['unbound_index'] = {'goal': [1, 1], 'proof': P.refl(1)}
negative['boolean_term'] = {'goal': [False, False], 'proof': P.refl(False)}
negative['float_term'] = {'goal': [0.0, 0.0], 'proof': P.refl(0.0)}
negative['string_term'] = {'goal': ['x', 'x'], 'proof': P.refl('x')}
negative['invalid_successor'] = {'goal': [[1, 0], [1, 0]], 'proof': P.refl([1, 0])}
negative['empty_term'] = {'goal': [[], []], 'proof': P.refl([])}
negative['extra_field'] = dict(positive['reflexivity'], irrelevant=0)
negative['bad_hypothesis_index'] = {'goal': [0, 0], 'proof': P.use(-1)}
negative['unbound_witness'] = {'goal': [[0, 0]], 'proof': ['i', [[0, 0]], -1, P.refl(0)]}
false_counter = P.I(0, 0, 1)
false_source = P.I(0, 0, P.S(1))
false_left = P.I(false_counter, 0, P.S(1))
negative['nonliteral_successor_counter'] = {
    'goal': [false_left, P.S(false_source)],
    'proof': ['v', P.refl(false_source), P.refl(false_left)]}
# The proposed equation is numerically 0=1. If the check that a counter
# is a two-element successor were erased, the other rule checks would pass.
negative['incorrect_evaluation_source'] = {'goal': [0, 0], 'proof': ['v', P.refl(0), P.refl(P.I(P.S(0), P.S(0), 1))]}
negative['malformed_proof_tag'] = {'goal': [0, 0], 'proof': [0, 0]}
negative['extra_proof_field'] = {'goal': [0, 0], 'proof': ['r', 0, 0]}
negative['native_q_not_public'] = {'goal': ['q', [0, 0]], 'proof': P.refl(0)}
# Replacing the used base with an unrelated reflexivity must invalidate Use.
bad = copy.deepcopy(positive['elimination_used_clause'])
def corrupt_use(data):
    if type(data) is list:
        if data and data[0] == 'u':
            return data[:3] + [P.refl(0)]
        return [corrupt_use(t) for t in data]
    return data
bad['proof'][3] = corrupt_use(bad['proof'][3])
negative['wrong_clause_antecedent'] = bad

results = {'positive': [], 'negative': [], 'translations': [], 'substitution': []}
for name, data in positive.items():
    assert C.verify(data)
    native = P.translate(data)
    assert N.verify(native)
    assert native['goal'] == data['goal']
    (EXAMPLES / (name + '.json')).write_text(json.dumps(data, separators=(',', ':')) + '\n')
    (EXAMPLES / (name + '.native.json')).write_text(json.dumps(native, separators=(',', ':')) + '\n')
    results['positive'].append(name)
    results['translations'].append(name)
for name, data in negative.items():
    assert expected_reject(data), name
    (EXAMPLES / ('reject_' + name + '.json')).write_text(json.dumps(data, separators=(',', ':')) + '\n')
    results['negative'].append(name)

# An open primary derivation and its ordinary formula/closure context have
# parameter -1. The eigenparameter is -2; after a closed substitution it
# must become -1, independently of whether the witness becomes literal zero.
open_ctx, target = P.intro_context(diag_goal, -1, [], 1)
open_branch = P.congr(target[0], P.use(0), open_ctx, 2)
open_proof = ['i', diag_goal, -1, open_branch]
assert C.derive(open_proof, [], 1) == diag_goal
images = [({-1: 0}, 0), ({-1: P.S(0)}, 0),
          ({-1: P.I(P.S(0), 0, P.S(1))}, 0),
          ({-1: -1}, 1), ({-1: P.S(-2)}, 2)]
for mapping, out_scope in images:
    image = P.substitute(open_proof, mapping, 1, out_scope)
    goal_image = P.substitute(diag_goal, mapping, 1, out_scope)
    assert C.derive(image, [], out_scope) == goal_image
    results['substitution'].append({'image': mapping[-1], 'scope': out_scope})

# Diagonal syntactic invariance on random well-formed formula matrices.
rng = random.Random(739251)
def random_term(scope, depth, fuel):
    if fuel == 0 or rng.random() < 0.45:
        return rng.randint(-scope, depth)
    if rng.random() < 0.4:
        return P.S(random_term(scope, depth, fuel - 1))
    return P.I(random_term(scope, depth, fuel - 1),
               random_term(scope, depth, fuel - 1),
               random_term(scope, depth + 1, fuel - 1))

guard_count = 0
for _ in range(600):
    scope = rng.randrange(1, 4)
    out_scope = rng.randrange(0, 4)
    matrix = [random_term(scope, 2, 3), random_term(scope, 2, 3)]
    if rng.random() < 0.5:
        matrix = [P.I(1, 1, random_term(scope, 3, 2)),
                  P.I(1, 1, random_term(scope, 3, 2))]
    assert C.formula(matrix, scope, 2)
    mapping = {-i: random_term(out_scope, 0, 2) for i in range(1, scope + 1)}
    image = P.substitute(matrix, mapping, scope, out_scope)
    assert C.formula(image, out_scope, 2)
    assert C.diagonal(matrix) == C.diagonal(image)
    guard_count += 1
results['guard_substitution_cases'] = guard_count

# An independently constructed old-mode case proof changes its required
# branch assumption when its variable witness is replaced by literal zero.
# This is a failure of literal proof-tree substitution, not inconsistency
# or failure of the old calculus's admissible substitution theorem.
old_body = W.opening(diag_goal[0], -1, 1)
old_assumption = W.opening(old_body, 0)
old_target = W.opening(old_body, P.S(-2))
old_context = [P.ordinary(old_assumption)]
old_branch = P.congr(old_target[0], P.use(0), old_context, 2)
old_proof = ['i', diag_goal, -1, old_branch]
assert W.derive(old_proof, [], 1) == diag_goal
old_image = P.substitute(old_proof, {-1: 0}, 1, 0)
try:
    W.derive(old_image, [], 0)
except Exception:
    results['witness_control_literal_substitution_failure'] = True
else:
    raise AssertionError('The old witness-mode counterexample should fail')
(EXAMPLES / 'open_witness_control.json').write_text(json.dumps({'scope':1,'goal':diag_goal,'proof':old_proof})+'\n')
(EXAMPLES / 'rejected_witness_control_substitution.json').write_text(json.dumps({'goal':diag_goal,'proof':old_image})+'\n')
(EXAMPLES / 'open_diagonal_substitution_source.json').write_text(json.dumps({'scope':1,'goal':diag_goal,'proof':open_proof})+'\n')
(EXAMPLES / 'closed_diagonal_substitution_result.json').write_text(json.dumps({'goal':diag_goal,'proof':P.substitute(open_proof,{-1:0},1,0)})+'\n')

# Opening controls use independently stated index-level expected answers.
opening_cases = [
    (P.I(1, 2, [0, 2]), -1, 0, P.I(-1, 1, [0, -1])),
    ([[4, 3]], -1, 1, [[-1, 3]]),
    ([P.I(0, 2, 2), 2], -1, 1, [P.I(0, -1, 2), -1]),
    ([P.I(0, -1, 2), -1], P.S(-2), 0, [P.I(0, -1, P.S(-2)), -1])]
for a, v, depth, expected in opening_cases:
    assert C.opening(a, v, depth) == expected, (a, v, depth)
results['opening_cases'] = len(opening_cases)

# Actual process acceptance and rejection, with and without assert removal.
process_count = 0
for module, table in [('checker.py', positive), ('native_diagonal_control.py',
                                                   {n: P.translate(d) for n,d in positive.items()})]:
    for mode in ([], ['-O']):
        for name, data in table.items():
            p = subprocess.run([sys.executable] + mode + [str(ROOT / module)],
                               input=json.dumps(data), text=True, capture_output=True)
            assert p.returncode == 0 and p.stdout == 'ACCEPT\n', (module, name, p)
            process_count += 1
for mode in ([], ['-O']):
    for name, data in negative.items():
        p = subprocess.run([sys.executable] + mode + [str(ROOT / 'checker.py')],
                           input=json.dumps(data), text=True, capture_output=True)
        assert p.returncode != 0 and p.stdout == 'REJECT\n', (name, p)
        process_count += 1
results['process_checks'] = process_count

skip = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.COMMENT,
        tokenize.NL, tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT}
class RemoveDocstrings(ast.NodeTransformer):
    def clean(self, node):
        self.generic_visit(node)
        if (node.body and isinstance(node.body[0], ast.Expr)
                and isinstance(node.body[0].value, ast.Constant)
                and isinstance(node.body[0].value.value, str)):
            del node.body[0]
        return node
    visit_Module = clean
    visit_FunctionDef = clean
    visit_AsyncFunctionDef = clean
    visit_ClassDef = clean

metrics = {}
for name in ('checker.py', 'native_diagonal_control.py', 'witness_control.py'):
    raw = (ROOT / name).read_bytes()
    tree = RemoveDocstrings().visit(ast.parse(raw))
    source = ast.unparse(tree) + '\n'
    metrics[name] = {'source_bytes': len(raw),
                     'source_gzip_9_bytes': len(gzip.compress(raw, compresslevel=9, mtime=0)),
                     'bytes': len(source.encode()),
                     'tokens': sum(t.type not in skip for t in tokenize.generate_tokens(io.StringIO(source).readline)),
                     'ast_nodes': sum(1 for _ in ast.walk(tree)),
                     'gzip_9_bytes': len(gzip.compress(source.encode(), compresslevel=9, mtime=0))}
    (ROOT / name.replace('.py', '.normalized.py')).write_text(source)
results['metrics'] = metrics
results['python'] = sys.version
results['status'] = 'all checks passed'
(ROOT / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
print(json.dumps(results, indent=2))

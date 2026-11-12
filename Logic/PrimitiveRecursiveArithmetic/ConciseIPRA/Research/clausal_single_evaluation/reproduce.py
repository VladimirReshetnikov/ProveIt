"""Proof translations and adversarial checks for the five-pattern UE calculus.

This is untrusted testing/reproduction code; no acceptance checker imports it.
"""
import ast
import copy
import gzip
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
HERE = ROOT / 'code'


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


raw = module('raw_ce5', ROOT / 'reference/raw_ce5.py')
forward = module('forward_ue', HERE / 'forward.py')
goal = module('goal_ue', HERE / 'checker.py')
raw_goal = module('raw_goal', HERE / 'raw_control.py')
zero_goal = module('zero_goal', HERE / 'zero_control.py')
independent = module('independent_normalized_e2', ROOT / 'reference/normalized_e2.py')


def normal(a):
    if type(a) is int:
        return a
    b = [normal(x) for x in a]
    return b[1] if len(b) == 3 and b[0] == 0 else b


def equation(p, g, n):
    e = forward.derive(p, g, n)
    if len(e) != 2:
        raise ValueError('equation expected')
    return e


def refl(t):
    return ['r', t]


def ue(p, q):
    return ['v', p, q]


def computation(c, a, h):
    predecessor = a if c == 0 else [c, a, h]
    return ue(refl(predecessor), refl([[0, c], a, h]))


def root(p, q, g, n):
    s, _ = equation(p, g, n)
    return ue(p, ue(q, refl([[0, 0], s, 1])))


def symmetry(p, g, n):
    s, _ = equation(p, g, n)
    return root(refl(s), p, g, n)


def congruence(h, p, g, n):
    s, _ = equation(p, g, n)
    frame = [[0, 0], s, h]
    return ue(p, ue(refl(s), refl(frame)))


def crossed(h, p, q, g, n):
    return root(congruence(h, p, g, n), q, g, n)


def transport(f, p, q, g, n):
    """From s=t and f(s), where f is an equation template, derive f(t)."""
    left, right = f
    return crossed(right, p, crossed(left, p, q, g, n), g, n)


def raw_to_uniform(p, source_context=None, target_context=None, n=0, replacements=None):
    """Map every raw CE5 proof to a UE proof of its zero-normal form.

    The only nonhomomorphic logical case is a nonzero raw witness which
    normalizes to zero. It is replaced by the surviving alias I(1,0,0).
    """
    g = [] if source_context is None else source_context
    k = [] if target_context is None else target_context
    replacements = {} if replacements is None else replacements
    tag = p[0]
    recurse = lambda q: raw_to_uniform(q, g, k, n, replacements)
    if tag == 'r':
        result = refl(normal(p[1]))
    elif tag == 'u':
        result = (copy.deepcopy(replacements[p[1]]) if p[1] in replacements else
                  ['u', p[1], normal(p[2]), recurse(p[3])])
    elif tag == 'v':
        first = raw.derive(p[1], g, n)
        second = raw.derive(p[2], g, n)
        major, minor = recurse(p[1]), recurse(p[2])
        result = root(major, minor, k, n) if second[0] == first[0] or second[0][0] == 0 else ue(major, minor)
    elif tag == 'e':
        paired = raw.derive(p[2], g, n)
        body = raw.opening(paired[0], -n - 1, 1)
        source_clause = (raw.opening(body, 0), body)
        target_body = normal(body)
        target_clause = (forward.opening(target_body, 0), target_body)
        branch = raw_to_uniform(p[3], g + [source_clause], k + [target_clause], n + 1, replacements)
        result = ['e', normal(p[1]), recurse(p[2]), branch]
    elif tag == 'i':
        a, t, branch = p[1:]
        b = raw.opening(a[0], t, 1)
        fresh = -n - 1
        source_eta = fresh if len(a[0]) == 2 and t == 0 else 0
        source_clause = ([0, 0], raw.opening(b, source_eta))
        target_a, target_t = normal(a), normal(t)
        exceptional = len(a[0]) == 2 and t != 0 and target_t == 0
        if exceptional:
            target_t = [[0, 0], 0, 0]
        target_b = forward.opening(target_a[0], target_t, 1)
        target_eta = fresh if len(target_a[0]) == 2 and target_t == 0 else 0
        target_clause = ([0, 0], forward.opening(target_b, target_eta))
        extended = k + [target_clause]
        overrides = dict(replacements)
        if exceptional:
            z_eq_zero = computation(0, 0, 0)
            local = ['u', len(k), 0, refl(0)]
            f = forward.opening(target_a[0], 0)
            overrides[len(g)] = transport(f, z_eq_zero, local, extended, n + 1)
        translated = raw_to_uniform(branch, g + [source_clause], extended, n + 1, overrides)
        if exceptional:
            f = forward.opening(target_a[0], [0, fresh])
            translated = transport(f, symmetry(computation(0, 0, 0), extended, n + 1), translated, extended, n + 1)
        result = ['i', target_a, target_t, translated]
    else:
        raise ValueError('unknown raw proof')
    actual = forward.derive(result, k, n)
    expected = normal(raw.derive(p, g, n))
    if actual != expected:
        raise ValueError('translation changed normalized conclusion')
    return result


def to_goal(p, g=None, n=0):
    g = [] if g is None else g
    tag = p[0]
    if tag == 'r':
        return None
    if tag == 'u':
        return ['u', p[1], p[2], to_goal(p[3], g, n)]
    if tag == 'v':
        _, t = equation(p[1], g, n)
        b, _ = equation(p[2], g, n)
        counter, seed, body = b
        return ['v', counter[1], seed, body, t, to_goal(p[1], g, n), to_goal(p[2], g, n)]
    if tag == 'e':
        paired = forward.derive(p[2], g, n)
        body = forward.opening(paired[0], -n - 1, 1)
        clause = (forward.opening(body, 0), body)
        return ['e', paired[0], to_goal(p[2], g, n), to_goal(p[3], g + [clause], n + 1)]
    if tag == 'i':
        a, t, branch = p[1:]
        body = forward.opening(a[0], t, 1)
        eta = -n - 1 if len(a[0]) == 2 and t == 0 else 0
        clause = ([0, 0], forward.opening(body, eta))
        return ['i', t, to_goal(branch, g + [clause], n + 1)]
    raise ValueError('bad proof')


def raw_to_goal(p, g=None, n=0):
    g = [] if g is None else g
    tag = p[0]
    if tag == 'r':
        return None
    if tag == 'u':
        return ['u', p[1], p[2], raw_to_goal(p[3], g, n)]
    if tag == 'v':
        s, t = raw.derive(p[1], g, n)
        b, _ = raw.derive(p[2], g, n)
        return ['v', b, s, t, raw_to_goal(p[1], g, n), raw_to_goal(p[2], g, n)]
    if tag == 'e':
        paired = raw.derive(p[2], g, n)
        body = raw.opening(paired[0], -n - 1, 1)
        clause = (raw.opening(body, 0), body)
        return ['e', paired[0], raw_to_goal(p[2], g, n), raw_to_goal(p[3], g + [clause], n + 1)]
    a, t, branch = p[1:]
    body = raw.opening(a[0], t, 1)
    eta = -n - 1 if len(a[0]) == 2 and t == 0 else 0
    clause = ([0, 0], raw.opening(body, eta))
    return ['i', t, raw_to_goal(branch, g + [clause], n + 1)]


def to_zero_goal(p, g=None, n=0):
    g = [] if g is None else g
    tag = p[0]
    if tag == 'r':
        return None
    if tag == 'u':
        return ['u', p[1], p[2], to_zero_goal(p[3], g, n)]
    if tag == 'v':
        s, t = forward.derive(p[1], g, n)
        b, _ = forward.derive(p[2], g, n)
        return ['v', b, s, t, to_zero_goal(p[1], g, n), to_zero_goal(p[2], g, n)]
    if tag == 'e':
        paired = forward.derive(p[2], g, n)
        body = forward.opening(paired[0], -n - 1, 1)
        clause = (forward.opening(body, 0), body)
        return ['e', paired[0], to_zero_goal(p[2], g, n), to_zero_goal(p[3], g + [clause], n + 1)]
    a, t, branch = p[1:]
    body = forward.opening(a[0], t, 1)
    eta = -n - 1 if len(a[0]) == 2 and t == 0 else 0
    clause = ([0, 0], forward.opening(body, eta))
    return ['i', t, to_zero_goal(branch, g + [clause], n + 1)]


def tagged(a, n, d=0, formula=False):
    if type(a) is int:
        return ['z'] if a == 0 else ['v', a - 1 if a > 0 else d + n + a]
    if formula:
        return ['d', tagged(a[0], n, d + 2, True)] if len(a) == 1 else ['='] + [tagged(x, n, d) for x in a]
    if len(a) == 2:
        return ['s', tagged(a[1], n, d)]
    return ['i', tagged(a[0], n, d), tagged(a[1], n, d), tagged(a[2], n, d + 1)]


def to_independent(p, g=None, kinds=None, n=0):
    """Translate clauses back to the independent normalized Eq/Q/D checker."""
    g = [] if g is None else g
    kinds = [] if kinds is None else kinds
    tag = p[0]
    rec = lambda q: to_independent(q, g, kinds, n)
    if tag == 'r':
        return ['refl', tagged(p[1], n)]
    if tag == 'v':
        return ['ev', rec(p[1]), rec(p[2])]
    if tag == 'u':
        h = ['hyp', len(g) - 1 - p[1]]
        return ['qe', tagged(p[2], n), h, rec(p[3])] if kinds[p[1]] == 'closure' else h
    if tag == 'e':
        paired = forward.derive(p[2], g, n)
        body = forward.opening(paired[0], -n - 1, 1)
        clause = (forward.opening(body, 0), body)
        return ['de', tagged(p[1], n, formula=True), rec(p[2]),
                to_independent(p[3], g + [clause], kinds + ['closure'], n + 1)]
    a, t, branch = p[1:]
    body = forward.opening(a[0], t, 1)
    eta = -n - 1 if len(a[0]) == 2 and t == 0 else 0
    clause = ([0, 0], forward.opening(body, eta))
    return ['di', tagged(a[0], n, 2, True), tagged(t, n),
            to_independent(branch, g + [clause], kinds + ['ordinary'], n + 1)]


def accepted(checker, certificate):
    try:
        checker.check(certificate)
        return True
    except Exception:
        return False


def metrics(path):
    text = path.read_text()
    tree = ast.parse(text)
    if isinstance(tree.body[0], ast.Expr) and isinstance(tree.body[0].value, ast.Constant) and isinstance(tree.body[0].value.value, str):
        tree.body.pop(0)
    data = (ast.unparse(tree) + '\n').encode()
    tokens = sum(t.type not in (tokenize.ENCODING, tokenize.ENDMARKER,
                 tokenize.NEWLINE, tokenize.NL, tokenize.INDENT,
                 tokenize.DEDENT, tokenize.COMMENT)
                 for t in tokenize.generate_tokens(io.StringIO(data.decode()).readline))
    packed = gzip.compress(data, compresslevel=9, mtime=0)
    return {'source': path.name, 'bytes': len(data), 'tokens': tokens,
            'ast_nodes': sum(1 for _ in ast.walk(tree)), 'gzip9_bytes': len(packed)}, data, packed


def main():
    positives = {p.stem: json.loads(p.read_text())
                 for p in sorted((ROOT / 'tests/raw').glob('*.json'))}

    # A nonliteral witness normalizing to zero must remain in case mode.
    # B(x,y) = I(y,x;u.x) = x. The branch uses B(t,0).
    raw_alias = [0, 0, 1]
    matrix = [[1, 2, 3], 2]
    source_goal = [matrix]
    body = raw.opening(matrix, raw_alias, 1)
    local_g = [([0, 0], raw.opening(body, 0))]
    local_h = ['u', 0, 0, refl(0)]
    source_c = [-1, raw_alias, raw_alias]
    redex = [[0, -1], raw_alias, raw_alias]
    # Raw Eval computes the successor iterator with a constant body.
    step = ['v', refl(source_c), refl(redex)]
    source = ['i', source_goal, raw_alias, step]
    positives['witness_normalizes_to_zero'] = {'goal': source_goal, 'proof': source}

    # This case really consumes the old zero-instance assumption. A naive
    # change to progress would supply I(z,0,0)=1 instead of the needed 0=1.
    matrix_false_base = [[1, 2, 3], [0, 2]]
    old_base = [0, raw_alias, raw_alias]
    local = ['u', 0, 0, refl(0)]
    base_compute = ['v', refl(raw_alias), refl(old_base)]
    seed_to_successor = ['v', local, base_compute]
    step_symmetry = ['v', refl(redex), step]
    consuming_step = ['v', seed_to_successor, step_symmetry]
    source_consuming = ['i', [matrix_false_base], raw_alias, consuming_step]
    positives['witness_collapse_consumes_base'] = {'goal': [matrix_false_base], 'proof': source_consuming}

    translated_cases = {}
    for name, certificate in positives.items():
        raw.verify(certificate)
        raw_goal.check({'goal': certificate['goal'], 'proof': raw_to_goal(certificate['proof'])})
        proof = raw_to_uniform(certificate['proof'])
        end = normal(certificate['goal'])
        forward.verify({'goal': end, 'proof': proof})
        out = {'goal': end, 'proof': to_goal(proof)}
        goal.check(out)
        zero_goal.check({'goal': end, 'proof': to_zero_goal(proof)})
        back = {'variables': 0, 'context': [], 'goal': tagged(end, 0, formula=True),
                'proof': to_independent(proof)}
        independent.check(back)
        translated_cases[name] = out

    # Closed derivation: induction really uses its current equation hypothesis.
    matrix = [[1, 0, 1], 0]
    g = [([0, 0], [[-1, 0, 1], 0])]
    hyp = ['u', 0, 0, refl(0)]
    comp = computation(-1, 0, 1)
    # comp is I(Sz,0,id)=I(z,0,id); compose it with the hypothesis.
    step = root(hyp, symmetry(comp, g, 1), g, 1)
    induction = ['i', [matrix], 0, step]
    induction_cert = {'goal': [matrix], 'proof': to_goal(induction)}
    goal.check(induction_cert)
    translated_cases['used_induction_hypothesis'] = induction_cert
    # Closure use at one and two, as well as fresh negative parameters.
    for k, target in enumerate((0, [0, 0], [0, [0, 0]])):
        end = [normal([target, 0, 1]), 0]
        proof = ['e', end, induction, ['u', 0, target, refl(0)]]
        out = {'goal': end, 'proof': to_goal(proof)}
        goal.check(out)
        translated_cases[f'closure_use_{k}'] = out

    leaf = {'goal': [0, 0], 'proof': None}
    rejects = {
        'false_equation': {'goal': [0, [0, 0]], 'proof': None},
        'extra_top_field': dict(leaf, other=0),
        'bool_scalar': {'goal': [False, False], 'proof': None},
        'float_scalar': {'goal': [0.0, 0.0], 'proof': None},
        'bool_successor': {'goal': [[False, 0], [False, 0]], 'proof': None},
        'future_parameter': {'goal': [-1, -1], 'proof': None},
        'unbound_index': {'goal': [1, 1], 'proof': None},
        'nonnormal_goal': {'goal': [[0, 0, 1], [0, 0, 1]], 'proof': None},
        'unknown_rule': {'goal': [0, [0, 0]], 'proof': ['unknown']},
        'missing_clause': {'goal': [0, [0, 0]], 'proof': ['u', 0, 0, None]},
        'bool_clause_index': {'goal': [0, [0, 0]], 'proof': ['u', False, 0, None]},
        'negative_clause_index': {'goal': [0, [0, 0]], 'proof': ['u', -1, 0, None]},
        'wrong_eval_target': {'goal': [0, [0, 0]], 'proof': ['v', 0, 0, 1, 0, None, None]},
        'wrong_eval_major': {'goal': [[[0, 0], 0, 1], [0, 0]], 'proof': ['v', 0, 0, 1, [0, 0], None, None]},
        'bool_eval_counter': {'goal': [[[0, 0], 0, 1], 0], 'proof': ['v', False, 0, 1, 0, None, None]},
        'eigen_witness_escape': {'goal': [[0, [0, 0]]], 'proof': ['i', -1, None]},
        'extra_argument': {'goal': [0, [0, 0]], 'proof': ['v', 0, 0, 1, 0, None, None, 0]},
        'eigen_goal_escape': {'goal': [0, [0, 0]], 'proof': ['e', matrix, to_goal(induction), None]},
    }
    # Atomic progress cannot be changed into case mode at witness one.
    mutation = copy.deepcopy(induction_cert)
    mutation['proof'][1] = [0, 0]
    rejects['progress_is_not_case'] = mutation
    # An Eq/D formula cannot be supplied where a numeric witness is required.
    rejects['formula_as_witness'] = {'goal': [matrix], 'proof': ['i', [[0, 0]], None]}
    for name, data in rejects.items():
        if accepted(goal, data):
            raise RuntimeError('invalid certificate accepted: ' + name)

    out = ROOT / 'evidence'
    out.mkdir(exist_ok=True)
    examples = ROOT / 'examples'
    examples.mkdir(exist_ok=True)
    source_examples = ROOT / 'tests/raw'
    source_examples.mkdir(exist_ok=True)
    for name, data in positives.items():
        (source_examples / (name + '.json')).write_text(json.dumps(data, indent=2) + '\n')
    runs = 0
    for optimized in (False, True):
        for name, data in list(translated_cases.items()) + list(rejects.items()):
            command = [sys.executable] + (['-O'] if optimized else []) + [str(HERE / 'checker.py')]
            run = subprocess.run(command, input=json.dumps(data), text=True, capture_output=True)
            expected = name in translated_cases
            if (run.returncode == 0) != expected or run.stdout.strip() != ('ACCEPT' if expected else 'REJECT'):
                raise RuntimeError('public-interface mismatch: ' + name)
            runs += 1
    for name, data in translated_cases.items():
        (examples / (name + '.json')).write_text(json.dumps(data, indent=2) + '\n')
    for name, data in rejects.items():
        (examples / ('reject_' + name + '.json')).write_text(json.dumps(data, indent=2) + '\n')
    measures = []
    for name in ('checker', 'raw_control', 'zero_control', 'forward', 'forward_raw_control'):
        record, data, packed = metrics(HERE / (name + '.py'))
        measures.append(record)
        (out / (name + '.normalized.py')).write_bytes(data)
        (out / (name + '.normalized.py.gz')).write_bytes(packed)
    result = {'positive': len(translated_cases), 'negative': len(rejects),
              'raw_to_canonical_and_independent_back_checks': len(positives),
              'public_cli_checks': runs, 'metrics': measures, 'python': sys.version}
    (out / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()

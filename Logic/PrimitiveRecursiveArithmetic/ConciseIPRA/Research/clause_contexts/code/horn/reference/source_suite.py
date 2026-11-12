"""Reproduce the controlled size comparison and executable clause certificates.

All proof builders are untrusted; each output is checked by an independent
standalone process. Mathematical equivalence is proved in the paper, not by
this finite test collection.
"""
import ast
import copy
import gzip
import hashlib
import io
import json
import pathlib
import subprocess
import sys
import tokenize

ROOT = pathlib.Path(__file__).resolve().parent
ZERO = 0
ONE = ['s', 0]


def I(n, a, h):
    return a if n == 0 else ['i', n, a, h]


def op(a, t, depth=0):
    if type(a) is int:
        if a <= depth:
            return a
        return t if a == depth + 1 else a - 1
    if a[0] == 's':
        return ['s', op(a[1], t, depth)]
    if a[0] == 'i':
        return I(op(a[1], t, depth), op(a[2], t, depth), op(a[3], t, depth + 1))
    if a[0] == '=':
        return ['=', op(a[1], t, depth), op(a[2], t, depth)]
    if a[0] == 'd':
        return ['d', op(a[1], t, depth + 2)]
    raise ValueError(a)


class Builder:
    def __init__(self, mode):
        self.mode = mode

    def refl(self, a):
        if self.mode == 'step':
            return a, a, ['r', a]
        c = self.comp(0, a, 1)
        return self.transport(c, c, 1)

    def step(self, p, q):
        _, c, a, h = q[0]
        if p[0] != I(c[1], a, h):
            raise ValueError('Builder predecessor mismatch')
        result = q[1], op(h, p[1])
        if self.mode == 'step':
            return *result, ['x', p[2], q[2]]
        computation = self.comp(c[1], a, h)
        bridge = self.transport(q, computation, 1)
        return self.transport(p, bridge, h)

    def comp(self, n, a, h):
        lhs = I(['s', n], a, h)
        rhs = op(h, I(n, a, h))
        if self.mode == 'control':
            return lhs, rhs, ['r', n, a, h]
        return self.step(self.refl(I(n, a, h)), self.refl(lhs))

    def resolve(self, p, q):
        if p[0] != q[0]:
            raise ValueError('Builder resolution mismatch')
        if self.mode == 'control':
            return self.transport(p, q, 1)
        j = I(ONE, p[0], 1)
        return self.step(p, self.step(q, self.refl(j)))

    def sym(self, p):
        return self.resolve(self.refl(p[0]), p)

    def trans(self, p, q):
        if p[1] != q[0]:
            raise ValueError('Builder transitivity mismatch')
        return self.resolve(q, self.sym(p))

    def transport(self, p, q, h):
        if q[0] != op(h, p[0]):
            raise ValueError('Builder transport mismatch')
        if self.mode == 'control':
            return q[1], op(h, p[1]), ['x', h, p[2], q[2]]
        bridge = self.trans(self.comp(0, p[0], h), q)
        return self.step(p, bridge)

    def use_equation(self, index, witness, premise, lhs, rhs):
        return lhs, rhs, ['u', index, witness, premise[2]]


def fixture(p):
    return {'goal': ['=', p[0], p[1]], 'proof': p[2]}


def positive_fixtures(mode):
    b = Builder(mode)
    cases = {}
    terms = [0, ONE, ['s', ONE], I(ONE, 0, ['s', 1]),
             I(ONE, ONE, I(1, ONE, ['s', 1]))]
    for i, a in enumerate(terms):
        cases[f'reflexivity_{i}'] = fixture(b.refl(a))
    for n_id, n in enumerate([0, ONE, ['s', ONE]]):
        for h_id, h in enumerate([1, 0, ['s', 1], I(ONE, 1, ['s', 1]),
                                 I(1, ONE, 1), I(I(1, 0, 1), ONE, 1)]):
            p = b.comp(n, ONE, h)
            cases[f'computation_{n_id}_{h_id}'] = fixture(p)
            cases[f'symmetry_{n_id}_{h_id}'] = fixture(b.sym(p))
            cases[f'resolution_{n_id}_{h_id}'] = fixture(b.resolve(p, p))
            h2 = I(1, ONE, ['s', 1])
            cases[f'transport_{n_id}_{h_id}'] = fixture(b.transport(p, b.refl(op(h2, p[0])), h2))

    matrix = ['=', 1, 1]
    dgoal = ['d', matrix]
    dproof = ['i', dgoal, 0, b.refl(['s', -1])[2]]
    cases['d_progress'] = {'goal': dgoal, 'proof': dproof}
    cases['d_case'] = {'goal': dgoal, 'proof': ['i', dgoal, ONE, b.refl(['s', -1])[2]]}
    cases['d_elimination_used_clause'] = {
        'goal': ['=', ONE, ONE],
        'proof': ['e', ['=', ONE, ONE], dproof, ['u', 0, ONE, b.refl(0)[2]]],
    }
    nested = ['d', dgoal]
    cases['nested_d_used_assumption'] = {
        'goal': nested,
        'proof': ['i', nested, 0, ['u', 0, 0, b.refl(0)[2]]],
    }
    matrix = ['=', I(1, ONE, 1), ONE]
    dgoal = ['d', matrix]
    old = b.use_equation(0, 0, b.refl(0), I(-1, ONE, 1), ONE)
    next_eq = b.trans(b.comp(-1, ONE, 1), old)
    inductive = ['i', dgoal, 0, next_eq[2]]
    cases['induction_uses_hypothesis'] = {'goal': dgoal, 'proof': inductive}
    cases['induction_instantiated_nested_counter'] = {
        'goal': ['=', I(terms[-1], ONE, 1), ONE],
        'proof': ['e', ['=', I(terms[-1], ONE, 1), ONE], inductive,
                  ['u', 0, terms[-1], b.refl(ONE)[2]]],
    }
    return cases


def negative_fixtures():
    b = Builder('step')
    good = fixture(b.refl(0))
    cases = {}
    for name, value in [('boolean', True), ('float', 0.0), ('null', None),
                        ('string', '0'), ('mapping', {}), ('negative_escape', -1),
                        ('positive_escape', 1), ('zero_counter', ['i', 0, 0, 1]),
                        ('body_escape', ['i', ONE, 0, 2])]:
        cases['bad_term_' + name] = {'goal': ['=', value, value], 'proof': ['r', value]}
    cases['wrong_top_keys'] = dict(good, extra=0)
    cases['bad_proof_tag'] = {'goal': good['goal'], 'proof': ['unknown', 0]}
    cases['extra_proof_field'] = {'goal': good['goal'], 'proof': ['r', 0, 0]}
    cases['step_root_fallback_forbidden'] = {'goal': good['goal'], 'proof': ['x', ['r', 0], ['r', 0]]}
    cases['step_wrong_predecessor'] = {
        'goal': ['=', I(['s', ONE], 0, 1), 0],
        'proof': ['x', ['r', 0], ['r', I(['s', ONE], 0, 1)]],
    }
    dgoal = ['d', ['=', 1, 1]]
    dproof = ['i', dgoal, 0, ['r', ['s', -1]]]
    cases['di_witness_escape'] = {'goal': dgoal, 'proof': ['i', dgoal, -1, ['r', ['s', -1]]]}
    cases['de_goal_escape'] = {'goal': ['=', -1, -1], 'proof': ['e', ['=', -1, -1], dproof, ['r', -1]]}
    for name, index in [('negative', -1), ('boolean', True), ('high', 1)]:
        cases['bad_clause_index_' + name] = {
            'goal': ['=', ONE, ONE],
            'proof': ['e', ['=', ONE, ONE], dproof, ['u', index, ONE, ['r', 0]]],
        }
    cases['wrong_clause_antecedent'] = {
        'goal': ['=', ONE, ONE],
        'proof': ['e', ['=', ONE, ONE], dproof, ['u', 0, ONE, ['r', ONE]]],
    }
    cases['false_equation'] = {'goal': ['=', 0, ONE], 'proof': ['r', 0]}
    cases['proof_not_array'] = {'goal': good['goal'], 'proof': {'r': 0}}
    return cases


def metrics(path):
    tree = ast.parse(path.read_text())
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            if node.body and isinstance(node.body[0], ast.Expr):
                value = node.body[0].value
                if isinstance(value, ast.Constant) and isinstance(value.value, str):
                    node.body.pop(0)
    normalized = (ast.unparse(tree) + '\n').encode()
    ignored = {tokenize.COMMENT, tokenize.ENCODING, tokenize.NL, tokenize.NEWLINE,
               tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}
    tokens = sum(t.type not in ignored for t in tokenize.generate_tokens(io.StringIO(normalized.decode()).readline))
    return {'tokens': tokens, 'ast_nodes': len(list(ast.walk(tree))), 'normalized_bytes': len(normalized),
            'gzip9_bytes': len(gzip.compress(normalized, compresslevel=9, mtime=0))}


def run_check(path, certificate, optimize):
    command = [sys.executable] + (['-O'] if optimize else []) + [str(path)]
    p = subprocess.run(command, input=json.dumps(certificate), text=True, capture_output=True, timeout=20)
    return p.returncode == 0 and p.stdout == 'ACCEPT\n'


def main():
    results = []
    out = ROOT / 'clausal_certificates'
    out.mkdir(exist_ok=True)
    for mode, filename in [('step', 'checker.py'), ('control', 'control_zero.py')]:
        cases = positive_fixtures(mode)
        target = out / mode
        target.mkdir(exist_ok=True)
        for name, certificate in cases.items():
            (target / (name + '.json')).write_text(json.dumps(certificate, separators=(',', ':')) + '\n')
            for optimize in [False, True]:
                accepted = run_check(ROOT / filename, certificate, optimize)
                results.append({'mode': mode, 'case': name, 'optimized': optimize, 'expected': True, 'accepted': accepted})
    negatives = negative_fixtures()
    target = out / 'negative'
    target.mkdir(exist_ok=True)
    for name, certificate in negatives.items():
        (target / (name + '.json')).write_text(json.dumps(certificate, separators=(',', ':')) + '\n')
        for optimize in [False, True]:
            accepted = run_check(ROOT / 'checker.py', certificate, optimize)
            results.append({'mode': 'step', 'case': name, 'optimized': optimize, 'expected': False, 'accepted': accepted})
    paths = ['checker.py', 'control_zero.py', 'control_raw.py',
             'reference/incoming_clausal.py', 'reference/current_eval.py']
    report = {'python': sys.version, 'metrics': {path: metrics(ROOT / path) for path in paths},
              'source_sha256': {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in paths},
              'checks': len(results), 'failures': [r for r in results if r['expected'] != r['accepted']],
              'results': results}
    (ROOT / 'clausal_verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'results'}, indent=2))
    return bool(report['failures'])


if __name__ == '__main__':
    sys.exit(main())

"""Untrusted finite checks for the matched diagonal/mirror proof checkers."""
import ast
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parents[1]
HERE = ROOT / 'code'

def load(name):
    spec = importlib.util.spec_from_file_location(name, HERE / (name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

M = load('mirror_six')
D = load('diagonal_six')
Z = ['z']
V = lambda i: ['v', i]
S = lambda a: ['s', a]
I = lambda c, a, h: ['i', c, a, h]
Eq = lambda a, b: ['=', a, b]

class Proofs:
    def __init__(self, n=0, g=()):
        self.n, self.g = n, list(g)
    def conclusion(self, p):
        return M.infer(p, self.g, self.n)
    def refl(self, a):
        return ['refl', a]
    def hyp(self, j):
        return ['hyp', j]
    def ev(self, p, q):
        return ['eval', p, q]
    def pivot(self, p, q):
        source = self.conclusion(p)[1]
        frame = I(Z, source, V(0))
        return self.ev(p, self.ev(q, self.refl(frame)))
    def sym(self, p):
        return self.pivot(self.refl(self.conclusion(p)[1]), p)
    def trans(self, p, q):
        return self.pivot(q, self.sym(p))
    def zero(self, a, h):
        return self.ev(self.refl(a), self.refl(I(Z, a, h)))
    def succ(self, c, a, h):
        return self.ev(self.refl(I(c, a, h)), self.refl(I(S(c), a, h)))
    def tr(self, h, p, q):
        source = self.conclusion(p)[1]
        previous = self.zero(source, h)
        previous_to_target = self.trans(previous, p)
        next_to_h_source = self.ev(previous, self.refl(I(S(Z), source, h)))
        next_to_output = self.trans(next_to_h_source, q)
        return self.ev(previous_to_target, next_to_output)
    def certificate(self, p, goal=None):
        return {'variables': self.n, 'context': self.g,
                'goal': self.conclusion(p) if goal is None else goal, 'proof': p}

def accepts(module, c):
    try:
        module.check(c)
        return True
    except Exception:
        return False

def metrics(path):
    raw = path.read_bytes()
    tree = ast.parse(raw)
    if isinstance(tree.body[0], ast.Expr) and isinstance(tree.body[0].value, ast.Constant) and isinstance(tree.body[0].value.value, str):
        tree.body.pop(0)
    normalized = ast.unparse(tree) + '\n'
    excluded = {tokenize.COMMENT, tokenize.ENCODING, tokenize.NL,
                tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT,
                tokenize.ENDMARKER}
    tokens = sum(t.type not in excluded for t in tokenize.generate_tokens(io.StringIO(normalized).readline))
    return {'normalized_bytes': len(normalized.encode()), 'tokens': tokens,
            'ast_nodes': sum(1 for _ in ast.walk(tree)),
            'source_sha256': hashlib.sha256(raw).hexdigest()}

def build():
    tests = {}
    p = Proofs(1)
    tests['refl_variable'] = (p.certificate(p.refl(V(0))), True, True)
    tests['zero_computation'] = (p.certificate(p.zero(V(0), S(V(0)))), True, True)
    tests['successor_computation'] = (p.certificate(p.succ(V(0), Z, S(V(0)))), True, True)
    p = Proofs(3, [Eq(V(0), V(1)), Eq(V(1), V(2))])
    tests['symmetry_from_hypothesis'] = (p.certificate(p.sym(p.hyp(0))), True, True)
    tests['transitivity_from_hypotheses'] = (p.certificate(p.trans(p.hyp(0), p.hyp(1))), True, True)
    template = I(V(0), V(0), V(1))
    source_instance = M.sub(template, V(0))
    tests['repeated_occurrence_congruence'] = (p.certificate(p.tr(template, p.hyp(0), p.refl(source_instance))), True, True)
    nested_template = I(V(0), V(1), I(V(0), V(1), S(V(2))))
    nested_source = M.sub(nested_template, V(0))
    tests['nested_iterator_binder_congruence'] = (p.certificate(p.tr(nested_template, p.hyp(0), p.refl(nested_source))), True, True)

    # The progressive mirror matrix 0 = I(y,0;u.u) actually consumes its IH.
    matrix = Eq(Z, I(V(0), Z, V(0)))
    branch = Proofs(1, [matrix])
    step = branch.sym(branch.ev(branch.sym(branch.hyp(0)), branch.refl(I(S(V(0)), Z, V(0)))))
    theorem = ['di', matrix, Z, step]
    p = Proofs()
    tests['mirror_progress_used_induction_hypothesis'] = (p.certificate(theorem), True, False)

    # A nonzero witness occurs in both the mirrored lhs and the initializer.
    witness_matrix = Eq(V(1), I(V(0), V(1), V(0)))
    witnessed = M.sub(['q', witness_matrix], S(Z))[1]
    witness_branch = Proofs(1, [witnessed])
    witness_step = witness_branch.sym(witness_branch.ev(witness_branch.sym(witness_branch.hyp(0)), witness_branch.refl(I(S(V(0)), S(Z), V(0)))))
    tests['mirror_progress_nonzero_witness'] = (p.certificate(['di', witness_matrix, S(Z), witness_step]), True, False)

    # Discharge the paired witness to obtain Q, then specialize its closure.
    closure = ['q', matrix]
    qproof = ['de', closure, theorem, ['hyp', 0]]
    tests['mirror_closure'] = (p.certificate(qproof), True, False)
    base = p.sym(p.zero(Z, V(0)))
    for target in [Z, S(Z), S(S(Z))]:
        qe = ['qe', target, qproof, base]
        tests['mirror_closure_at_' + str(len(tests))] = (p.certificate(qe), True, False)

    # A compound matrix uses cases in both calculi.
    compound = ['q', Eq(V(0), V(0))]
    tests['compound_case_intro'] = (p.certificate(['di', compound, Z, ['hyp', 0]]), True, True)

    # Witness substitution can CREATE the mirror shape. The mode is tested
    # before that substitution, so this proof must use its ZERO base.
    becomes_mirror = Eq(V(1), I(V(0), Z, V(0)))
    opened_zero_base = Eq(Z, I(Z, Z, V(0)))
    branch = Proofs(1, [opened_zero_base])
    base_consumed = branch.trans(branch.hyp(0), branch.zero(Z, V(0)))
    # Reuse the closed closure proof in the larger ambient scope.
    shifted_qproof = qproof
    specialized = ['qe', S(V(0)), shifted_qproof, branch.sym(branch.zero(Z, V(0)))]
    repaired_step = branch.trans(base_consumed, specialized)
    cases_proof = ['di', becomes_mirror, Z, repaired_step]
    tests['guard_test_before_witness_substitution'] = (p.certificate(cases_proof), True, False)

    false_equation = {'variables': 0, 'context': [], 'goal': Eq(Z, S(Z)), 'proof': ['refl', Z]}
    tests['reject_false_equation'] = (false_equation, False, False)
    tests['reject_bool_variable'] = ({'variables': True, 'context': [], 'goal': Eq(Z, Z), 'proof': ['refl', Z]}, False, False)
    tests['reject_out_of_scope_witness'] = ({'variables': 0, 'context': [], 'goal': ['d', compound], 'proof': ['di', compound, V(0), ['hyp', 0]]}, False, False)
    tests['reject_eigenparameter_escape'] = ({'variables': 0, 'context': [], 'goal': Eq(V(0), V(0)), 'proof': ['de', Eq(V(0), V(0)), theorem, ['refl', V(0)]]}, False, False)
    tests['reject_wrong_eval_source'] = (p.certificate(['eval', ['refl', S(Z)], ['refl', I(Z, Z, V(0))]], Eq(I(Z, Z, V(0)), S(Z))), False, False)
    tests['reject_malformed_iterator_body'] = ({'variables': 0, 'context': [], 'goal': Eq(Z, Z), 'proof': ['refl', I(Z, Z, V(1))]}, False, False)
    tests['reject_extra_proof_argument'] = ({'variables': 0, 'context': [], 'goal': Eq(Z, Z), 'proof': ['refl', Z, Z]}, False, False)
    tests['reject_extra_top_field'] = (dict(false_equation, hidden=[]), False, False)
    return tests

def main():
    tests = build()
    fixture_dir = ROOT / 'examples' / 'direct'
    fixture_dir.mkdir(parents=True, exist_ok=True)
    outcomes = []
    for name, (certificate, mirror_expected, diagonal_expected) in tests.items():
        path = fixture_dir / (name + '.json')
        path.write_text(json.dumps(certificate, indent=2) + '\n')
        for label, module, expected in [('mirror_six', M, mirror_expected), ('diagonal_six', D, diagonal_expected)]:
            actual = accepts(module, certificate)
            if actual != expected:
                raise AssertionError((name, label, expected, actual))
            for optimize in [False, True]:
                argv = [sys.executable] + (['-O'] if optimize else []) + [str(HERE / (label + '.py'))]
                run = subprocess.run(argv, input=json.dumps(certificate), text=True, capture_output=True)
                cli_accepts = run.returncode == 0 and run.stdout.strip() == 'ACCEPT'
                if cli_accepts != expected:
                    raise AssertionError((name, label, optimize, run.returncode, run.stdout, run.stderr))
            outcomes.append({'test': name, 'checker': label, 'expected_acceptance': expected})
    report = {'scope': 'Finite implementation checks; not a proof of the universal equivalence theorem.',
              'python': sys.version, 'fixture_count': len(tests), 'api_checks': len(outcomes),
              'cli_checks': 2 * len(outcomes), 'unexpected_outcomes': 0,
              'metrics': {name: metrics(HERE / (name + '.py')) for name in ['diagonal_six', 'mirror_six']},
              'outcomes': outcomes}
    (ROOT / 'evidence' / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'outcomes'}, indent=2))

if __name__ == '__main__':
    main()

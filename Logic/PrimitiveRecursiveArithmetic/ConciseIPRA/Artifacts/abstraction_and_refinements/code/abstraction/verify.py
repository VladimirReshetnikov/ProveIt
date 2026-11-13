"""Scope, abstraction, marker, and complete CLI checks; standard library only."""
from pathlib import Path
import ast, copy, importlib.util, io, json, subprocess, sys, tokenize

ROOT = Path(__file__).resolve().parent
def load(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / (name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module
C = load('checker')

def metric(path):
    tree = ast.parse(path.read_text())
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)) and node.body and isinstance(node.body[0], ast.Expr) and isinstance(node.body[0].value, ast.Constant) and isinstance(node.body[0].value.value, str):
            node.body.pop(0)
    normalized = ast.unparse(tree) + '\n'
    ignored = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}
    return {'tokens': sum(x.type not in ignored for x in tokenize.generate_tokens(io.StringIO(normalized).readline)), 'ast_nodes': sum(1 for _ in ast.walk(tree)), 'normalized_bytes': len(normalized.encode())}

def terms(n):
    base = [[]] + list(range(n))
    return base + [[a] for a in base] + [[[], a, 0] for a in base] + [[a, [], []] for a in base]

def formulas(n):
    ts = terms(n)
    result = [[t, u] for t in ts[:5] for u in ts[:5]]
    result += [[0, 0, [i, i]] for i in range(n + 1)]
    result += [[[i, i]] for i in range(n + 2)]
    result += [[0, 0, [[i, 0]]] for i in range(n + 3)]
    return result

checks = 0
for n in range(3):
    for goal in formulas(n):
        assert C.formula_ok(goal, n)
        for term in terms(n):
            body = C.abstract_formula(goal, term)
            assert C.formula_ok(body, n + 1)
            assert C.substitute_formula(body, term) == goal
            assert C.substitute_formula(body, []) == C.replace_formula(goal, term, [])
            context = [[0, 0, body], C.substitute_formula(body, [])]
            proof = {'rule': 'aqe', 'term': term, 'major': {'rule': 'hyp', 'index': 0}, 'base': {'rule': 'hyp', 'index': 1}}
            C.verify(n, context, goal, proof)
            checks += 1

def size(tree):
    return 1 + sum(map(size, tree)) if isinstance(tree, list) else 1

marker_checks = 0
for n in range(3):
    for body in formulas(n + 1):
        for term in terms(n)[:5]:
            tail = []
            for _ in range(size(body) + 1):
                tail = [tail]
            marker = [[], term, tail]
            goal = C.substitute_formula(body, marker)
            assert C.abstract_formula(goal, marker) == body
            marker_checks += 1

# A free parameter and a locally bound variable have distinct occurrences.
assert C.replace_formula([[0, 0]], 0, []) == [[0, 0]]
assert C.replace_formula([[2, 0]], 0, []) == [[[], 0]]
assert C.replace_formula([0, 0, [0, 1]], 0, []) == [0, 0, [0, []]]

def hyp(i): return {'rule': 'hyp', 'index': i}
def refl(t):
    eq = [[[], t, []], t]
    return {'rule': 'brep', 'equality': eq, 'major': {'rule': 'i0'}, 'minor': {'rule': 'i0'}}

def universal_refl():
    matrix = [0, 0]
    major = {'rule': 'di', 'witness': [], 'premise': refl([0])}
    return {'rule': 'de', 'matrix': matrix, 'major': major, 'branch': hyp(0)}

def theorem(goal, proof):
    return {'n': 0, 'context': [], 'goal': goal, 'proof': proof}

one = [[]]
aqe = theorem([one, one], {'rule': 'aqe', 'term': one, 'major': universal_refl(), 'base': refl([])})
previous_iterator = [0, [], 0]
step_iterator = [[0], [], 0]
step_computation = [step_iterator, previous_iterator]
symmetry = {'rule': 'brep', 'equality': step_computation, 'major': {'rule': 'is'}, 'minor': {'rule': 'is'}}
progress = {'rule': 'brep', 'equality': [previous_iterator, []], 'major': hyp(0), 'minor': symmetry}
induction = theorem([[[0, [], 0], []]], {'rule': 'di', 'witness': [], 'premise': progress})
compound = theorem([[0, 0, [[], []]]], {'rule': 'di', 'witness': [], 'premise': hyp(0)})

cases = [
    ('aqe_reflexivity', aqe, True),
    ('used_equation_induction', induction, True),
    ('compound_case_introduction', compound, True),
    ('computation_zero', theorem([[[], one, 0], one], {'rule': 'i0'}), True),
    ('unproved_contradiction', theorem([[], one], {'rule': 'i0'}), False),
]
for name, term in [('future_parameter', 0), ('boolean_term', False), ('float_term', 0.0), ('string_term', '0')]:
    bad = copy.deepcopy(aqe)
    bad['proof']['term'] = term
    cases.append((name, bad, False))
bad = copy.deepcopy(aqe); bad['proof']['body'] = [0, 0]
cases.append(('obsolete_body_field', bad, False))
bad = copy.deepcopy(aqe); bad['proof']['major']['branch']['index'] = 1
cases.append(('invalid_hypothesis', bad, False))
bad = copy.deepcopy(aqe); bad['goal'] = [[], one]
cases.append(('false_inferred_matrix', bad, False))
bad = copy.deepcopy(aqe); bad['n'] = 1
cases.append(('open_sequent_at_closed_driver', bad, False))
bad = copy.deepcopy(induction); bad['proof']['premise']['minor'] = hyp(0)
cases.append(('forged_induction_step', bad, False))

fixtures = ROOT / 'fixtures'; fixtures.mkdir(exist_ok=True)
executions = []
for name, data, expected in cases:
    path = fixtures / (name + '.json')
    encoded = json.dumps(data, separators=(',', ':')) + '\n'
    path.write_text(encoded)
    for optimized in (False, True):
        command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT / 'checker.py')]
        run = subprocess.run(command, input=encoded, text=True, capture_output=True, timeout=10)
        accepted = run.returncode == 0 and run.stdout == 'ACCEPT\n'
        if accepted != expected:
            raise RuntimeError((name, optimized, run.returncode, run.stdout, run.stderr))
        executions.append({'case': name, 'optimized': optimized, 'expected_accept': expected, 'accepted': accepted})

report = {'python': sys.version.split()[0], 'abstraction_and_open_inference_checks': checks, 'oversized_marker_checks': marker_checks, 'explicit_capture_checks': 3, 'cli_executions': executions, 'metrics': {name: metric(ROOT / name) for name in ['checker.py', 'control.py', 'control_eight_rules.py']}, 'scope': 'Finite syntactic and operational checks, not a formal proof of universal soundness or the iPRA bridge.'}
(ROOT / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: v for k, v in report.items() if k != 'cli_executions'}, indent=2))
print('CLI executions:', len(executions), 'all passed')

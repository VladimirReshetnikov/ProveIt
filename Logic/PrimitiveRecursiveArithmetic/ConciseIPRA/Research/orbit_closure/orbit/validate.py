"""Regression tests and measured full-module comparisons; untrusted driver."""
from pathlib import Path
from copy import deepcopy
import ast
import gzip
import importlib.util
import io
import json
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('translate_ur', ROOT / 'translate_ur.py')
T = importlib.util.module_from_spec(spec)
spec.loader.exec_module(T)
Z = ['z']
V = lambda i: ['v', i]
S = lambda a: ['s', a]
I = lambda n, a, h: ['i', n, a, h]
E = lambda a, b: ['=', a, b]

def cert(n, goal, proof, context=None):
    return {'variables': n, 'context': context or [], 'goal': goal, 'proof': proof}

def run(name, value, expected, tag, optimized):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT / 'code' / (name + '.py'))]
    result = subprocess.run(command, input=json.dumps(value), text=True, capture_output=True, timeout=10)
    accepted = result.returncode == 0 and result.stdout == 'ACCEPT\n'
    return {'case': tag, 'checker': name, 'optimized': optimized, 'expected': expected, 'accepted': accepted, 'exit': result.returncode}

cases = []
source_record = json.loads((ROOT / 'reference' / 'validation.json').read_text())
for row in source_record['results']:
    if row['checker'] != 'scalar_ur.py' or row['optimized']:
        continue
    name = row['case']
    value = json.loads((ROOT / 'reference' / 'examples' / ('scalar_ur_' + name + '.json')).read_text())
    cases.append(('scalar_ur', value, row['expected_accept'], 'source_' + name))
    if row['expected_accept']:
        for mode in ('inferred', 'templates'):
            target = deepcopy(value)
            target['proof'] = T.translate(target['proof'], mode)
            cases.append(('orbit_' + mode, target, True, 'translate_' + name))
            (ROOT / 'validation' / ('translated_' + mode + '_' + name + '.json')).write_text(json.dumps(target, indent=2) + '\n')
            if value['proof'][0] == 'ur':
                _, f, h, _, p = value['proof']
                op = ['orbit', T.orbit_formula(f, h), T.translate(p, mode)] if mode == 'inferred' else ['orbit', f, h, T.translate(p, mode)]
                closure = cert(value['variables'], T.orbit_formula(f, h), op, value['context'])
                cases.append(('orbit_' + mode, closure, True, 'direct_' + name))

# The premise and conclusion explicitly use a passive parameter beneath
# nested iterator binders. Translating the inherited nested fixture covers it.
identity = cert(0, T.orbit_formula(V(0), S(V(0))), ['orbit', T.orbit_formula(V(0), S(V(0))), T.refl(S(V(0)))])
cases.append(('orbit_inferred', identity, True, 'closed_identity_orbit'))

bad = deepcopy(identity)
bad['proof'][1][1][2][2] = S(Z)
bad['goal'] = deepcopy(bad['proof'][1])
cases.append(('orbit_inferred', bad, False, 'wrong_initializer'))

# Critical counter-dependence attack: f(y)=y, h(y,u)=S(y).
# The recurrence f(Sz)=S(z) is reflexive, but the asserted orbit would give
# 1 = I(1,0;u.2)=2. Reject the extra counter coordinate before the premise.
bad = cert(0, ['q', E(V(0), I(V(0), Z, S(V(1))))], ['orbit', ['q', E(V(0), I(V(0), Z, S(V(1))))], T.refl(S(V(0)))])
cases.append(('orbit_inferred', bad, False, 'counter_dependent_update'))

bad = deepcopy(identity)
bad['proof'][1][1][2][1] = S(V(0))
bad['goal'] = deepcopy(bad['proof'][1])
cases.append(('orbit_inferred', bad, False, 'wrong_counter_shape'))
bad = deepcopy(identity)
bad['proof'][-1] = ['hyp', 0]
cases.append(('orbit_inferred', bad, False, 'no_induction_hypothesis'))
bad = deepcopy(identity)
bad['proof'][-1] = T.refl(V(0))
cases.append(('orbit_inferred', bad, False, 'wrong_recurrence'))
bad = deepcopy(identity)
bad['proof'][1][1][1] = ['q', E(Z, Z)]
bad['goal'] = deepcopy(bad['proof'][1])
cases.append(('orbit_inferred', bad, False, 'formula_as_term'))
bad = deepcopy(identity)
bad['proof'][1][1][1] = V(True)
bad['goal'] = deepcopy(bad['proof'][1])
cases.append(('orbit_inferred', bad, False, 'boolean_variable'))
bad = deepcopy(identity)
bad['proof'][1][1][2][3] = S(V(2))
bad['goal'] = deepcopy(bad['proof'][1])
cases.append(('orbit_inferred', bad, False, 'out_of_scope_update'))
bad = deepcopy(identity)
bad['proof'][1][1][2][3] = I(V(0), Z, S(V(2)))
bad['goal'] = deepcopy(bad['proof'][1])
cases.append(('orbit_inferred', bad, False, 'nested_counter_capture'))

# Ordinary full-logical rule fixtures are replayed for both Orbit kernels,
# including existential eigenvariable escape and exact integer scope typing.
for row in source_record['results']:
    if row['checker'] != 'baseline_qi.py' or row['optimized'] or row['case'].startswith('qi_'):
        continue
    value = json.loads((ROOT / 'reference' / 'examples' / ('baseline_qi_' + row['case'] + '.json')).read_text())
    for name in ('orbit_inferred', 'orbit_templates'):
        cases.append((name, value, row['expected_accept'], 'common_' + row['case']))

records = []
for name, value, expected, tag in cases:
    for opt in (False, True):
        records.append(run(name, value, expected, tag, opt))
    if name == 'orbit_inferred' and tag in ('counter_dependent_update','nested_counter_capture','closed_identity_orbit'):
        (ROOT / 'validation' / (tag + '.json')).write_text(json.dumps(value, indent=2) + '\n')

# Translator CLI checks actual JSON I/O, not just direct Python calls.
source_path = ROOT / 'reference' / 'examples' / 'scalar_ur_ur_nested_iterator_scope.json'
cli_checks = []
for mode in ('inferred', 'templates'):
    result = subprocess.run([sys.executable, str(ROOT / 'translate_ur.py'), mode], input=source_path.read_text(), text=True, capture_output=True, timeout=10)
    ok = result.returncode == 0
    if ok:
        check = subprocess.run([sys.executable, str(ROOT / 'code' / ('orbit_' + mode + '.py'))], input=result.stdout, text=True, capture_output=True, timeout=10)
        ok = check.returncode == 0 and check.stdout == 'ACCEPT\n'
    cli_checks.append({'mode': mode, 'accepted': ok})

excluded = {tokenize.COMMENT, tokenize.INDENT, tokenize.DEDENT, tokenize.NEWLINE, tokenize.NL, tokenize.ENDMARKER, tokenize.ENCODING}
metrics = []
for name in ('scalar_ur', 'orbit_templates', 'orbit_inferred'):
    s = ast.unparse(ast.parse((ROOT / 'code' / (name + '.py')).read_text())) + '\n'
    metrics.append({'file': name + '.py', 'normalized_bytes': len(s.encode()), 'tokens': sum(t.type not in excluded for t in tokenize.generate_tokens(io.StringIO(s).readline)), 'ast_nodes': sum(1 for _ in ast.walk(ast.parse(s))), 'gzip9': len(gzip.compress(s.encode(), compresslevel=9, mtime=0))})
summary = {'python': sys.version, 'process_checks': len(records), 'expected_acceptances': sum(r['expected'] for r in records), 'expected_rejections': sum(not r['expected'] for r in records), 'mismatches': sum(r['accepted'] != r['expected'] for r in records), 'translator_cli_checks': cli_checks, 'metrics': metrics, 'results': records}
(ROOT / 'validation' / 'results.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps({k:v for k,v in summary.items() if k != 'results'}, indent=2))
for row in records:
    if row['expected'] != row['accepted']:
        print('MISMATCH', row)
sys.exit(bool(summary['mismatches']) or not all(r['accepted'] for r in cli_checks))

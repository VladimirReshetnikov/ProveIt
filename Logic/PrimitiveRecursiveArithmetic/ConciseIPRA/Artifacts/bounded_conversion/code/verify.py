"""End-to-end checks of bounded conversion and comparison via head normal forms.

The compiler is untrusted proof-producing code. The seven-rule checker imports
neither this file nor the six-rule control. This suite is finite evidence.
"""
import ast
import hashlib
import importlib.util
import io
import json
import subprocess
import sys
import tokenize
from pathlib import Path

ROOT = Path(__file__).resolve().parent
FIX = ROOT / 'fixtures'
FIX.mkdir(exist_ok=True)


def load(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / (name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


old = load('control')
Z = ['z']
V = lambda k: ['v', k]
S = lambda t: ['s', t]
I = lambda n, a, h: ['i', n, a, h]
E = lambda a, b: ['=', a, b]
D = lambda a: ['d', a]
Q = lambda a: ['q', a]


def convert_proof(p):
    """Erase local steps and normalize stored formula templates only."""
    if not isinstance(p, list) or not p:
        return p
    match p:
        case ['cv', _, _, branch]:
            return convert_proof(branch)
        case ['vs', j, t, u, left, right]:
            return ['vs', j, t, u, convert_proof(left), convert_proof(right)]
        case ['qe', b, t, left, right]:
            return ['qe', old.normal(b), t, convert_proof(left), convert_proof(right)]
        case ['de', b, major, branch]:
            return ['de', old.normal(b), convert_proof(major), convert_proof(branch)]
        case ['di', t, branch]:
            return ['di', t, convert_proof(branch)]
    return p


def convert_data(data):
    return dict(variables=data['variables'],
                context=[old.normal(a) for a in data['context']],
                goal=old.normal(data['goal']), proof=convert_proof(data['proof']))


cases = []


def case(name, n, context, goal, proof, accepted=True, compare=True):
    data = dict(variables=n, context=context, goal=goal, proof=proof)
    path = FIX / (name + '.json')
    path.write_text(json.dumps(data, separators=(',', ':')) + '\n')
    cases.append(dict(name=name, path=path.name, accepted=accepted,
                      compare=compare and accepted))


case('reflexivity', 1, [], E(V(0), V(0)), None)
case('hypothesis', 2, [E(V(0), V(1))], E(V(0), V(1)), None)
r = I(Z, V(0), V(0))
case('zero_contraction', 1, [], E(r, V(0)), ['cv', r, 0, None])
case('reverse_zero_contraction', 1, [], E(V(0), r), ['cv', r, 0, None])
r = I(S(V(0)), V(1), S(V(0)))
t = S(I(V(0), V(1), S(V(0))))
case('successor_contraction', 2, [], E(r, t), ['cv', r, 0, None])
# The binder in an iterator body is preserved when substituting a recursive call.
r = I(S(Z), V(0), I(V(0), V(1), V(1)))
t = I(I(Z, V(0), I(V(0), V(1), V(1))), V(0),
      old.shift(I(Z, V(0), I(V(0), V(1), V(1)))))
case('successor_nested_binder', 1, [], E(r, t), ['cv', r, 0, None])
for depth in range(5):
    r, t = I(Z, V(0), V(0)), V(0)
    for _ in range(depth):
        r, t = I(r, Z, V(0)), I(t, Z, V(0))
    case('counter_depth_' + str(depth), 1, [], E(r, t),
         ['cv', r, depth, None], depth <= 3)
    if depth <= 3:
        case('counter_depth_' + str(depth) + '_reverse', 1, [], E(t, r),
             ['cv', r, depth, None])
for label, depth in [('negative', -1), ('float', 0.0), ('boolean', False), ('string', '0')]:
    r = I(Z, V(0), V(0))
    case('invalid_depth_' + label, 1, [], E(r, V(0)),
         ['cv', r, depth, None], False)
inner = I(Z, Z, V(0))
r = I(V(0), inner, V(0))
t = I(V(0), Z, V(0))
case('forbidden_seed_conversion', 1, [], E(r, t), ['cv', r, 1, None], False)
case('unrelated_endpoint', 1, [], E(V(0), S(V(0))),
     ['cv', I(Z, Z, V(0)), 0, None], False)
# The final goal is true and well formed. Each bad hint occurs in a
# detour that an unchecked erasing contraction could traverse; rejection
# therefore checks the hint boundary rather than just a false conclusion.
good = I(Z, Z, V(0))
for label, bad_body in [('out_of_scope', V(1)), ('malformed', ['v', True])]:
    bad = I(Z, Z, bad_body)
    case('erased_' + label + '_hint', 0, [], E(Z, good),
         ['cv', bad, 0, ['cv', bad, 0, ['cv', good, 0, None]]], False)
case('missing_conversion_branch', 1, [], E(I(Z, V(0), V(0)), S(V(0))),
     ['cv', I(Z, V(0), V(0)), 0, None], False)
case('variable_substitution', 2, [E(V(0), V(1))], E(S(V(0)), S(V(1))),
     ['vs', 0, V(1), S(V(0)), None, None])
case('simultaneous_self_occurrence', 1, [E(V(0), S(V(0)))],
     E(S(V(0)), S(S(V(0)))), ['vs', 0, S(V(0)), S(V(0)), None, None])
case('nonvariable_substitution_index', 2, [E(V(0), V(1))],
     E(S(V(0)), S(V(1))), ['vs', ['v', 0], V(1), S(V(0)), None, None], False)
case('future_variable_substitution', 2, [E(V(0), V(1))],
     E(S(V(0)), S(V(1))), ['vs', 2, V(1), S(V(0)), None, None], False)
b = E(I(V(0), V(1), V(2)), V(1))
base_redex = I(Z, V(0), V(1))
case('closure_elimination', 1, [Q(b)], E(I(V(0), V(0), V(1)), V(0)),
     ['qe', b, V(0), None, ['cv', base_redex, 0, None]])
case('unproved_closure_major', 1, [], E(I(V(0), V(0), V(1)), V(0)),
     ['qe', b, V(0), None, ['cv', base_redex, 0, None]], False)
b = E(I(V(0), Z, V(0)), Z)
step = I(S(V(0)), Z, V(0))
case('progress_used_hypothesis', 0, [], D(b), ['di', Z, ['cv', step, 0, None]])
case('compound_case_introduction', 0, [], D(D(E(Z, Z))),
     ['di', Z, ['di', Z, None]])
case('out_of_scope_witness', 0, [], D(E(Z, Z)), ['di', V(0), None], False)
# Fresh witness 0; old parameters shift to 1 and 2. The self-substitution
# supplies symmetry without adding an equality assumption about the witness.
case('symmetry_via_dummy_discharge', 2, [E(V(0), V(1))], E(V(1), V(0)),
     ['de', E(Z, Z), ['di', Z, None], ['vs', 0, V(0), V(1), None, None]])
case('discharge_cannot_invent_equation', 1, [], E(V(0), Z),
     ['de', E(Z, Z), ['di', Z, None], None], False)
case('closed_contradiction', 0, [], E(Z, S(Z)), None, False)

# The separately produced, substantive transport packet is mandatory.
packet = FIX / 'transport_packet.json'
if not packet.is_file():
    raise FileNotFoundError("Run build_transport_packet.py to create the transport fixture")
cases.append(dict(name='transport_packet', path=packet.name,
                  accepted=True, compare=True))


def run(program, data, optimized):
    command = [sys.executable, '-I', '-S', '-B']
    if optimized:
        command.append('-O')
    result = subprocess.run(command + [str(ROOT / program)],
                            input=json.dumps(data).encode(),
                            capture_output=True, timeout=30)
    accepted = result.returncode == 0 and result.stdout == b'ACCEPT\n'
    return accepted


results = []
for item in cases:
    data = json.loads((FIX / item['path']).read_text())
    for optimized in (False, True):
        got = run('checker.py', data, optimized)
        results.append(dict(fixture=item['name'], program='checker.py',
                            optimized=optimized, accepted=got,
                            expected=item['accepted'], passed=got == item['accepted']))
        if item['compare']:
            compiled = convert_data(data)
            got = run('control.py', compiled, optimized)
            results.append(dict(fixture=item['name'], program='control.py',
                                optimized=optimized, accepted=got,
                                expected=True, passed=got))

SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
        tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def metric(name):
    raw = (ROOT / name).read_bytes()
    source = ast.unparse(ast.parse(raw)) + '\n'
    return dict(file=name, raw_bytes=len(raw),
                significant_tokens=sum(t.type not in SKIP for t in
                    tokenize.generate_tokens(io.StringIO(source).readline)),
                ast_nodes=len(list(ast.walk(ast.parse(source)))),
                normalized_bytes=len(source.encode()),
                sha256=hashlib.sha256(raw).hexdigest())


report = dict(python=sys.version, fixtures=len(cases), executions=len(results),
              failed_expectations=sum(not r['passed'] for r in results),
              metrics=[metric('control.py'), metric('checker.py')],
              scope='Finite checks; the calculus-equivalence theorem is a written proof, not inferred from these tests.',
              comparison='Local conversion is erased and formula templates head-normalized by an untrusted producer; whole raw acceptance languages differ.',
              results=results)
(ROOT / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
(FIX / 'manifest.json').write_text(json.dumps(cases, indent=2) + '\n')
print(json.dumps({k: v for k, v in report.items() if k != 'results'}, indent=2))
for item in results:
    if not item['passed']:
        print('FAILED', item)
if report['failed_expectations']:
    raise SystemExit(1)

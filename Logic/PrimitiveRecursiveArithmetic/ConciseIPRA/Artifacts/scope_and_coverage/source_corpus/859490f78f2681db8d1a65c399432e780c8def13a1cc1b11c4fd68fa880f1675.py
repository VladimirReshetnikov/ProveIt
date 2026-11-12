"""Finite complete-process checks for the new composition family.

Producers are untrusted and derive from the pinned current corpus.
The tests never import the trusted checkers into their own interpreter.
"""
import ast
import gzip
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent.parent


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    sys.modules[name] = result
    spec.loader.exec_module(result)
    return result


arity = module('producer', ROOT / 'reference/arity_producer.py')
arity_tests = module('arity_tests', ROOT / 'reference/arity_cases.py')
uniform = module('uniform_producer', ROOT / 'reference/uniform_producer.py')
translate = module('affine_translate', ROOT / 'reference/affine_translate.py')


def affine_packet(packet):
    out = []
    for m, s, u, t in packet[:-1]:
        if m:
            out.append([translate.formula(m), translate.term(s),
                        translate.term(u), translate.formula(t)])
        elif m is None:
            out.append([None, *translate.term([s, u, t])])
        else:
            out.append([m, s, u, translate.term(t)])
    return out + [translate.formula(packet[-1])]


def run(checker, data, optimized=False):
    result = subprocess.run([sys.executable] + (['-O'] if optimized else []) +
                            [str(ROOT / checker)], input=data,
                            text=True, capture_output=True, timeout=12)
    accepted = result.returncode == 0 and result.stdout.strip() == 'ACCEPT'
    return accepted, result.returncode, result.stdout, result.stderr


def main():
    cases_by_checker = {}
    cases_by_checker['code/checker_tokens.py'] = arity_tests.build_cases()
    originals = uniform.build_cases()
    def nonvacuous_zero_witness(P):
        x, y, z, u = 'new_zero_x', 'new_zero_y', 'new_zero_z', 'new_zero_u'
        def loop(n, seed):
            return P.I(n, seed, u, P.V(u))
        body = P.Eq(loop(P.V(y), P.V(x)), 0)
        premise = P.transitivity(P.compute(loop(P.S(P.V(z)), 0)),
                                 P.hyp(P.Eq(loop(P.V(z), 0), 0)),
                                 'new_zero_transport')
        proof = P.introduction(P.D(x, y, body), 0, z, 'progress', premise)
        emitter = P.Emitter()
        packet = emitter.packet(proof)
        return dict(name='direct_nonvacuous_zero_witness', accept=True,
                    meaning='A literal zero DI witness is used by the matrix and retained IH.',
                    packet=packet, proof_tree=proof, trace=emitter.trace)
    originals.append(nonvacuous_zero_witness(uniform))
    affine_cases = []
    for case in originals:
        copied = dict(case)
        copied['packet'] = affine_packet(case['packet'])
        if case['name'] == 'two_child_counter_constant_update':
            # The canonical translator erases binary numerical zero aliases.
            # Both source and goal now become the genuine I0(0,0;0)=0 axiom.
            copied['name'] = 'canonicalized_binary_zero_becomes_I0'
            copied['accept'] = True
            copied['meaning'] = 'Canonical translation erases a binary zero alias in both packet and goal, yielding I0.'
        affine_cases.append(copied)
    affine_cases.extend([
        dict(name='untranslated_binary_counter_mismatch', accept=False,
             packet=[[None, [0, 0], 0, 0], [[[0, 0], 0, 0], 0]]),
        dict(name='high_arity_false_goal_no_DI', accept=False,
             packet=[[[], 0, 0, [0]], [0, 0, [0, 0], 0]]),
        dict(name='successor_source_cannot_prove_I0', accept=False,
             packet=[[None, [0], 0, 0], [[0, 0, 0], 0]])
    ])
    cases_by_checker['code/checker.py'] = affine_cases
    cases_by_checker['code/checker_portable.py'] = affine_cases
    # Re-encode the same named derivations using arity scopes. The instruction
    # dispatcher and zero-predecessor expansion are the uniform producer's.
    uniform.Emitter.term = arity.Emitter.term
    uniform.Emitter.formula = arity.Emitter.formula
    old_emit = uniform.Emitter.emit
    import inspect
    method = inspect.getsource(old_emit)
    import textwrap
    method = textwrap.dedent(method).replace('[1, major[1]]', '[3, major[1]]')
    namespace = dict(uniform.__dict__)
    exec(method, namespace)
    uniform.Emitter.emit = namespace['emit']
    cases_by_checker['code/checker_ast.py'] = uniform.build_cases() + [nonvacuous_zero_witness(uniform)]
    rows = []
    for checker, cases in cases_by_checker.items():
        for case in cases:
            data = json.dumps(case['packet'])
            for optimized in (False, True):
                accepted, code, stdout, stderr = run(checker, data, optimized)
                matched = accepted == case['accept']
                if not accepted:
                    matched = matched and code != 0 and 'ACCEPT' not in stdout
                rows.append(dict(checker=checker, name=case['name'],
                                 optimized=optimized, expected=case['accept'],
                                 accepted=accepted, passed=matched,
                                 diagnostic=stderr if not matched else ''))
        for data in ('', '{', 'null', '[]', '{}', '[null]', '[true]', '["a"]'):
            for optimized in (False, True):
                accepted, code, stdout, stderr = run(checker, data, optimized)
                rows.append(dict(checker=checker, name='malformed_' + repr(data),
                                 optimized=optimized, expected=False,
                                 accepted=accepted,
                                 passed=not accepted and code != 0 and 'ACCEPT' not in stdout))
    output = dict(scope='Finite CLI checks; not a proof of universal soundness.',
                  runs=len(rows), passed=sum(row['passed'] for row in rows), rows=rows)
    (ROOT / 'evidence/validation.json').write_text(json.dumps(output, indent=2) + '\n')
    (ROOT / 'tests/cases.json').write_text(json.dumps(cases_by_checker, indent=2) + '\n')
    print(json.dumps({k: v for k, v in output.items() if k != 'rows'}))
    failed = [row for row in rows if not row['passed']]
    if failed:
        print(json.dumps(failed, indent=2))
        raise SystemExit(1)


if __name__ == '__main__':
    main()

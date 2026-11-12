"""Reproduce the packet proof, head-conversion boundary, and rejection tests.

Finite executable checks complement the universal proofs in the report.
The normalizers and proof checkers are not inferred from these checks.
"""
import copy
import importlib.util
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
BASE = ROOT.parent


def load(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / (name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


Z = ['z']
ONE = ['s', Z]
TWO = ['s', ONE]


def var(i):
    return ['v', i]


def equation(s, t):
    return ['=', s, t]


def weak(m, proof, amount=1, depth=0):
    if proof is None:
        return None
    tag, *a = proof
    shift = lambda x, extra=0: m.shift(x, amount, depth + extra)
    recur = lambda p: weak(m, p, amount, depth)
    if tag == 'vs':
        j, t, u, p, q = a
        return [tag, j + (amount if j >= depth else 0), shift(t), shift(u), recur(p), recur(q)]
    if tag == 'qe':
        b, t, p, q = a
        return [tag, shift(b, 1), shift(t), recur(p), recur(q)]
    if tag == 'de':
        b, p, q = a
        return [tag, shift(b, 2), recur(p), weak(m, q, amount, depth + 1)]
    t, p = a
    return [tag, shift(t), weak(m, p, amount, depth + 1)]


def selector(m, n, a, b):
    return ['i', n, a, m.shift(b)]


def parity(m, n):
    return ['i', n, Z, selector(m, var(0), ONE, Z)]


def cases(m, body, target, zero, successor):
    body = m.normal(body)
    dummy = m.shift(body, 1, 1)
    closure = ['de', dummy, ['di', ONE, successor], None]
    return ['qe', body, target, closure, zero]


def transport(m, s, t, h, r, major, minor):
    """Construct full crossed transport from six primitive rule families."""
    hs = m.sub(h, s)
    inner_left = selector(m, parity(m, var(0)), var(1), m.shift(h))
    inner_right = selector(m, parity(m, var(0)), m.shift(t, 2), m.shift(r, 2))
    matrix = m.normal(equation(selector(m, var(0), Z, inner_left),
                               selector(m, var(0), Z, inner_right)))
    body = equation(selector(m, var(0), m.shift(s, 2), m.shift(hs, 2)),
                    selector(m, var(0), m.shift(t, 2), m.shift(r, 2)))
    branch = cases(m, body, parity(m, ['s', var(0)]),
                   weak(m, major), weak(m, minor, 2))
    introduction = ['di', s, branch]
    use = lambda target: ['qe', matrix, target, None, None]
    return ['de', matrix, introduction, ['vs', 0, m.shift(t), h, use(TWO), use(ONE)]]


def accepted(m, certificate):
    try:
        m.check(copy.deepcopy(certificate))
        return True
    except Exception:
        return False


def certificate(m, n, context, goal, proof):
    return {'variables': n, 'context': [m.normal(a) for a in context],
            'goal': m.normal(goal), 'proof': proof}


def main():
    results = []
    fixture_dir = BASE / 'tests' / 'head'
    fixture_dir.mkdir(parents=True, exist_ok=True)

    def record(name, condition):
        if not condition:
            raise AssertionError(name)
        results.append(name)

    for mode in ['head', 'full']:
        m = load(mode + '_checker')
        s, t, r = var(0), var(1), var(2)
        templates = [var(0), Z, ['s', var(0)],
                     ['i', var(0), Z, var(0)],
                     ['s', ['i', Z, var(0), var(0)]],
                     ['i', var(3), var(1), var(1)],
                     ['i', var(3), ['i', Z, var(0), var(0)],
                      ['s', ['i', Z, var(1), var(0)]]]]
        for number, h in enumerate(templates):
            context = [equation(s, t), equation(m.sub(h, s), r)]
            p = transport(m, s, t, h, r, None, None)
            c = certificate(m, 4, context, equation(r, m.sub(h, t)), p)
            record(mode + '_transport_' + str(number), accepted(m, c))
            if mode == 'head':
                (fixture_dir / ('transport_' + str(number) + '.json')).write_text(json.dumps(c, indent=2) + '\n')
            enlarged = certificate(m, 5, [m.shift(a) for a in context],
                                   m.shift(equation(r, m.sub(h, t))), weak(m, p))
            record(mode + '_transport_weakened_' + str(number), accepted(m, enlarged))

        # Raw zero and a raw zero alias must both work as packet witnesses.
        for number, s in enumerate([Z, ['i', Z, Z, var(0)], ['i', Z, var(0), var(0)]]):
            h = ['s', var(0)]
            context = [equation(s, t), equation(m.sub(h, s), r)]
            p = transport(m, s, t, h, r, None, None)
            c = certificate(m, 3, context, equation(r, m.sub(h, t)), p)
            record(mode + '_raw_witness_' + str(number), accepted(m, c))
            if mode == 'head':
                (fixture_dir / ('raw_witness_' + str(number) + '.json')).write_text(json.dumps(c, indent=2) + '\n')

        # All six primitives: hypothesis, reflexivity, VS, QE, DE, Intro.
        body = equation(var(0), var(0))
        dbody = m.shift(body, 1, 1)
        c = certificate(m, 0, [], ['d', dbody], ['di', Z, None])
        record(mode + '_progress_introduction', accepted(m, c))
        c = certificate(m, 0, [], ['d', ['d', m.shift(dbody)]], ['di', ONE, ['di', ONE, None]])
        record(mode + '_compound_cases', accepted(m, c))

    m = load('head_checker')
    redex = ['i', Z, var(0), var(0)]
    suspended = ['s', redex]
    record('head_keeps_redex_under_successor', m.normal(suspended) == suspended)
    record('full_contracts_redex_under_successor', load('full_checker').normal(suspended) == ['s', var(0)])
    c = certificate(m, 1, [], equation(['s', var(0)], suspended),
                    ['vs', 0, redex, ['s', var(0)], None, None])
    record('raw_hint_conversion_bridge', accepted(m, c))
    (fixture_dir / 'raw_hint_conversion_bridge.json').write_text(json.dumps(c, indent=2) + '\n')

    good = certificate(m, 1, [], equation(var(0), var(0)), None)
    bad = []
    c = copy.deepcopy(good)
    c['variables'] = True
    bad.append(('boolean_scope', c))
    c = copy.deepcopy(good)
    c['goal'] = equation(var(1), var(1))
    bad.append(('free_variable_escape', c))
    c = certificate(m, 0, [], equation(Z, ONE), None)
    bad.append(('contradiction', c))
    for name, body in [('erased_scope', var(99)), ('erased_sort', equation(Z, Z))]:
        t = ['i', Z, var(0), body]
        c = certificate(m, 1, [], equation(['s', var(0)], ['s', t]),
                        ['vs', 0, t, ['s', var(0)], None, None])
        bad.append((name, c))
    # Here the public context and goal themselves are valid. Only a raw hint
    # contains the defect, and head conversion would erase it if the required
    # prevalidation were deleted. These isolate hint validation from parsing
    # and public-goal validation.
    for field in ['replacement', 'minor']:
        for defect, body in [('scope', var(99)), ('sort', equation(Z, Z))]:
            t = ['i', Z, var(0), body] if field == 'replacement' else var(0)
            u = ['i', Z, var(1), body] if field == 'minor' else var(1)
            c = certificate(m, 3, [equation(var(1), var(2))],
                            equation(var(2), var(1)), ['vs', 0, t, u, None, None])
            bad.append(('isolated_' + field + '_' + defect, c))
    c = certificate(m, 1, [], equation(var(0), ONE), ['vs', True, ONE, var(0), None, None])
    bad.append(('boolean_variable_index', c))
    c = certificate(m, 1, [], equation(var(0), ONE), ['vs', -1, ONE, var(0), None, None])
    bad.append(('negative_variable_index', c))
    naming = m.normal(equation(selector(m, var(0), Z, var(1)),
                               selector(m, var(0), Z, ONE)))
    leak = ['de', naming, ['di', ONE, None], ['qe', naming, ONE, None, None]]
    bad.append(('paired_witness_escape', certificate(m, 1, [], equation(var(0), ONE), leak)))
    for name, c in bad:
        record('reject_' + name, not accepted(m, c))
        (fixture_dir / ('reject_' + name + '.json')).write_text(json.dumps(c, indent=2) + '\n')

    # Check actual CLI and optimized Python on every generated fixture.
    for f in sorted(fixture_dir.glob('*.json')):
        want = not f.name.startswith('reject_')
        for options in [[], ['-O']]:
            p = subprocess.run([sys.executable, *options, str(ROOT / 'head_checker.py')],
                               input=f.read_bytes(), stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=20)
            ok = p.returncode == 0 and p.stdout == b'ACCEPT\n'
            record(('cli_optimized_' if options else 'cli_') + f.stem, ok == want)
    evidence = {'checks': len(results), 'passed': len(results), 'names': results,
                'status': 'finite regression evidence; universal equivalence is a written theorem'}
    (BASE / 'evidence').mkdir(exist_ok=True)
    (BASE / 'evidence' / 'head_checks.json').write_text(json.dumps(evidence, indent=2) + '\n')
    print(json.dumps({'checks': len(results), 'passed': len(results)}))


if __name__ == '__main__':
    main()

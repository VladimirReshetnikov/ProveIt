"""Reproducible, independent checking of translated proof certificates."""

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'code'))
import native_checker as native
import diagonal_checker as diagonal
import translate as t


def congr(template, proof, source):
    value = t.sub(template, source)
    return ['tr', t.shift(value), template, proof, t.refl(value)]


def identity_induction():
    y = t.V(0)
    value = t.I(y, t.Z, t.S(t.V(0)))
    equation = t.Eq(value, y)
    computation = ['succ', y, t.Z, t.S(t.V(0))]
    step = t.trans(computation, congr(t.S(t.V(0)), t.hyp(0), value),
                   t.I(t.S(y), t.Z, t.S(t.V(0))))
    return {'variables': 0, 'context': [], 'goal': t.Q(equation),
            'proof': ['qi', equation, step]}


def conditional_seed_induction():
    # E(0) is a=b, with distinct free parameters.  It is not an axiom or
    # a theorem of the empty retained context.  The progress hypothesis is used.
    y, a, b = t.V(0), t.V(1), t.V(2)
    h = t.S(t.V(0))
    left, right = t.I(y, a, h), t.I(y, b, h)
    equation = t.Eq(left, right)
    next_left, next_right = t.I(t.S(y), a, h), t.I(t.S(y), b, h)
    left_computation, right_computation = ['succ', y, a, h], ['succ', y, b, h]
    middle = congr(t.S(t.V(0)), t.hyp(0), left)
    step = t.trans(t.trans(left_computation, middle, next_left),
                   t.symm(right_computation, next_right), next_left)
    return {'variables': 2, 'context': [], 'goal': t.Q(equation),
            'proof': ['qi', equation, step]}


def contextual_update_induction():
    # Gamma contains c=d.  Both that retained equation and the current
    # induction equation are needed to compare iterators with different updates.
    y, a, b, c, d = [t.V(i) for i in range(5)]
    hs = t.S(t.V(0))
    hc = t.I(t.V(4), t.V(0), hs)
    hd = t.I(t.V(5), t.V(0), hs)
    left, right = t.I(y, a, hc), t.I(y, b, hd)
    equation = t.Eq(left, right)
    next_left, next_right = t.I(t.S(y), a, hc), t.I(t.S(y), b, hd)
    lc, rc = ['succ', y, a, hc], ['succ', y, b, hd]
    change_state = congr(t.I(t.shift(c), t.V(0), hs), t.hyp(0), left)
    change_parameter = congr(t.I(t.V(0), t.shift(right), hs), t.hyp(1), c)
    middle = t.trans(change_state, change_parameter, t.I(c, left, hs))
    step = t.trans(t.trans(lc, middle, next_left), t.symm(rc, next_right), next_left)
    return {'variables': 4, 'context': [t.Eq(t.V(2), t.V(3))],
            'goal': t.Q(equation), 'proof': ['qi', equation, step]}


def instantiate_certificate(c, sigma, variables):
    return {'variables': variables,
            'context': [t.map_ast(a, sigma) for a in c['context']],
            'goal': t.map_ast(c['goal'], sigma),
            'proof': t.map_proof(c['proof'], sigma)}


def tags(p):
    found = {p[0]}
    locations = {'tr': (3, 4), 'qe': (2, 3), 'de': (2, 3),
                 'di': (3,), 'qi': (2,)}.get(p[0], ())
    for i in locations:
        found |= tags(p[i])
    return found


def encoded_size(c):
    return len((json.dumps(c, separators=(',', ':')) + '\n').encode())


def main():
    folder = ROOT / 'tests' / 'translation_certificates'
    folder.mkdir(exist_ok=True)
    receipts = []
    coverage = {'native': set(), 'diagonal': set()}
    checks = 0

    def run_case(c, source, name, save=False, cli=False):
        nonlocal checks
        src, dst = (native, diagonal) if source == 'native' else (diagonal, native)
        src.check(c)
        checks += 1
        coverage[source] |= tags(c['proof'])
        out = t.translate_certificate(c, source)
        dst.check(out)
        checks += 1
        back_source = 'diagonal' if source == 'native' else 'native'
        back = t.translate_certificate(out, back_source)
        src.check(back)
        checks += 1
        if (out['variables'], out['context'], out['goal']) != (
                c['variables'], c['context'], c['goal']):
            raise ValueError('Translation changed the sequent')
        receipt = {'name': name, 'source': source, 'source_rules': sorted(tags(c['proof'])),
                   'source_bytes': encoded_size(c), 'translated_bytes': encoded_size(out),
                   'roundtrip_bytes': encoded_size(back), 'status': 'accepted'}
        if save:
            for suffix, cert in [('source', c), ('translated', out), ('roundtrip', back)]:
                path = folder / (name + '_' + suffix + '.json')
                path.write_text(json.dumps(cert, separators=(',', ':')) + '\n')
        if cli:
            target_name = 'diagonal_checker.py' if source == 'native' else 'native_checker.py'
            data = json.dumps(out, separators=(',', ':'))
            for option in ([], ['-O']):
                proc = subprocess.run([sys.executable, *option, str(ROOT / 'code' / target_name)],
                                      input=data, text=True, capture_output=True, timeout=30)
                if proc.returncode or proc.stdout != 'ACCEPT\n':
                    raise ValueError('CLI check failed: ' + name + ' ' + proc.stderr)
                checks += 1
            receipt['normal_and_optimized_cli'] = 'accepted'
        receipts.append(receipt)

    examples = {
        'identity_induction': identity_induction(),
        'conditional_seed_induction': conditional_seed_induction(),
        'contextual_update_induction': contextual_update_induction(),
    }
    for name, c in examples.items():
        run_case(c, 'native', name, save=True, cli=True)

    # Instantiations that exercise passive parameters, nested term binders,
    # numeral substitution, and retained-context substitution.
    substitutions = [
        ('seed_zero_and_successor', examples['conditional_seed_induction'],
         lambda i: t.Z if i == 0 else t.S(t.V(0)), 1),
        ('seed_nested_iterators', examples['conditional_seed_induction'],
         lambda i: t.I(t.V(0), t.S(t.Z) if i == 0 else t.Z,
                       t.I(t.V(0), t.V(1), t.S(t.V(0)))), 1),
        ('context_closed_parameters', examples['contextual_update_induction'],
         lambda i: t.Z if i == 0 else t.S(t.Z), 0),
    ]
    for name, c, sigma, variables in substitutions:
        run_case(instantiate_certificate(c, sigma, variables), 'native', name, save=True)

    # The other producer uses named syntax, independent of this compiler.
    for path in sorted((ROOT / 'tests' / 'certificates').glob('*.json')):
        c = json.loads(path.read_text())
        for source, checker in [('native', native), ('diagonal', diagonal)]:
            try:
                checker.check(c)
            except (ValueError, TypeError, IndexError, KeyError, RecursionError):
                continue
            run_case(c, source, path.stem)

    expected = {'native': {'hyp', 'zero', 'succ', 'tr', 'qe', 'de', 'di', 'qi'},
                'diagonal': {'hyp', 'zero', 'succ', 'tr', 'qe', 'de', 'di'}}
    if coverage != expected:
        raise ValueError('Missing source-rule coverage: ' + repr(coverage))
    result = {'python': sys.version.split()[0], 'certificate_cases': len(receipts),
              'checker_executions': checks,
              'source_rule_coverage': {k: sorted(v) for k, v in coverage.items()},
              'all_passed': True, 'cases': receipts,
              'limits': ['Finite executable checks are not a proof-assistant verification.',
                         'The translators expand proof trees; no polynomial size bound is claimed.',
                         'Every translated sequent is checked by the destination standalone checker.']}
    (ROOT / 'evidence' / 'translation_tests.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ['certificate_cases', 'checker_executions',
                                           'source_rule_coverage', 'all_passed']}, indent=2))


if __name__ == '__main__':
    main()

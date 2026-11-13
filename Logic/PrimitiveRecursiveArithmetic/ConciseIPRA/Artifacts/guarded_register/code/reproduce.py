"""Reproduce the strict checker comparison and finite/symbolic checks."""
import ast
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent


def module(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / (name + '.py'))
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def fixtures(kind):
    m = module('checker_' + kind)
    S, eq = m.succ, m.eq
    lift = lambda a, n: m.subst(a, delta=n)

    def refl(t):
        p = ['i0', t, 0] if kind == 'i' else ['js', 0, lift(t, 1)]
        return ['tr', 1, p, p]

    good = {}
    def add(name, proof):
        goal = m.prove(proof)
        m.formula(goal, 0)
        good[name] = [goal, proof]

    add('zero_reflexivity', refl(0))
    add('successor_reflexivity', refl(S(0)))
    body = eq(0, 0)
    d = ['di', body, 0, ['hyp', 0]]
    add('case_introduction', d)
    q = ['de', d, ['hyp', 0]]
    add('witness_discharge', q)
    add('closure_elimination', ['qe', S(0), q, refl(0)])
    add('equational_progress', ['qi', eq(1, 1), refl(S(1))])
    add('progress_at_successor', ['qe', S(0), good['equational_progress'][1], refl(0)])
    if kind == 'i':
        add('zero_computation', ['i0', S(0), S(1)])
        add('successor_computation', ['is', 0, 0, S(1)])
        p = ['i0', 0, 0]
    else:
        add('initialization_constant', ['j0', S(0)])
        add('initialization_successor_body', ['j0', S(1)])
        add('load_constant', ['js', 0, 0])
        add('load_state_dependent', ['js', 0, 1])
        W = lambda x: ['j', S(0), lift(x, 1)]
        add('W_successor_closure', ['qi', eq(W(S(1)), 1), ['js', 0, S(2)]])
        add('W_successor_base', ['js', 0, 0])
        p = ['js', 0, 0]
    source = m.prove(p)[1]
    add('crossed_transport', ['tr', S(1), p, refl(S(source))])

    bad = {
        'free_root_variable': [eq(1, 1), refl(0)],
        'boolean_variable': [eq(True, True), refl(0)],
        'future_witness': [['d', body], ['di', body, 1, ['hyp', 0]]],
        'quantified_induction': [['q', ['d', body]], ['qi', ['d', body], d]],
        'missing_hypothesis': [eq(0, 0), ['hyp', 0]],
        'wrong_goal': [eq(0, S(0)), refl(0)],
        'unknown_rule': [eq(0, 0), ['refl', 0]],
        'negative_variable': [eq(-1, 0), refl(0)],
        'extra_rule_field': [eq(0, 0), ['hyp', 0, 0]],
        'ill_typed_formula': [['=', ['q', body], 0], refl(0)],
    }
    dx = ['di', eq(2, 2), 0, ['hyp', 0]]
    bad['escaping_witness'] = [eq(0, 0), ['de', dx, ['qe', 0, ['hyp', 0], refl(1)]]]
    if kind == 'j':
        # The public result is valid: the bad term occurs only in an auxiliary
        # arithmetic axiom, so this catches missing guard validation in j0.
        bad_base = ['j0', 1]
        bad['unguarded_base_auxiliary'] = [eq(S(0), S(0)), ['tr', 1, bad_base, bad_base]]
        bad['unguarded_state_body'] = [eq(['j', 0, 1], 0), refl(0)]
        bad['unguarded_counter_dependence'] = [eq(['j', 0, ['j', 1, S(0)]], 0), refl(0)]
        bad['malformed_successor_body'] = [eq(['j', 0, ['j', 1]], 0), refl(0)]
        bad['extra_successor_body_field'] = [eq(['j', 0, ['j', 1, 0, 0]], 0), refl(0)]
        bad['removed_increment_rule'] = [eq(0, 0), ['inc', 0, 0, refl(0)]]
        bad['old_conditional_load_rule'] = [eq(0, 0), ['load', 0, S(0), refl(S(0))]]
        bad['future_update_parameter'] = [eq(0, 0), ['js', 0, 2]]
        # Guarded terms remain guarded under substitution for outer parameters.
        state_free = ['j', 1, 2]
        successor_headed = ['j', 1, S(1)]
        m.term(state_free, 1)
        m.term(successor_headed, 1)
        m.term(m.subst(state_free, (S(0),)), 0)
        m.term(m.subst(successor_headed, (S(0),)), 0)
        nested_state_free = ['j', 1, ['j', 2, 0]]
        m.term(nested_state_free, 1)
        m.term(m.subst(nested_state_free, (S(0),)), 0)
        assert m.subst(['j', 1, 2], delta=1) == ['j', 2, 3]
    else:
        assert m.subst(['i', 1, 1, 2], delta=1) == ['i', 2, 2, 3]
    assert m.subst(['d', eq(2, 3)], (S(0),)) == ['d', eq(2, S(0))]
    return good, bad


def metrics(path):
    tree = ast.parse(path.read_text())
    source = ast.unparse(tree) + '\n'
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
               tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    return {'tokens': sum(t.type not in ignored for t in tokenize.generate_tokens(io.StringIO(source).readline)),
            'ast_nodes': len(list(ast.walk(tree))), 'normalized_bytes': len(source.encode())}


def main():
    records = []
    for kind in ('i', 'j'):
        good, bad = fixtures(kind)
        for expected, data in ((True, good), (False, bad)):
            for name, payload in data.items():
                folder = ROOT / 'certificates' / kind / ('positive' if expected else 'negative')
                folder.mkdir(parents=True, exist_ok=True)
                path = folder / (name + '.json')
                path.write_text(json.dumps(payload, separators=(',', ':')) + '\n')
                for optimized in (False, True):
                    command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT / ('checker_' + kind + '.py'))]
                    result = subprocess.run(command, input=path.read_text(), capture_output=True, text=True, timeout=10)
                    accepted = result.returncode == 0 and result.stdout == 'ACCEPT\n'
                    assert accepted == expected, (kind, name, optimized, result.stderr)
                    records.append({'checker': kind, 'fixture': name, 'optimized': optimized, 'accepted': accepted})
    result = {'python': sys.version, 'metrics': {k: metrics(ROOT / ('checker_' + k + '.py')) for k in ('i', 'j')},
              'test_runs': len(records), 'accepted': sum(r['accepted'] for r in records),
              'rejected': sum(not r['accepted'] for r in records), 'mismatches': 0, 'runs': records}
    (ROOT / 'evidence.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'runs'}, indent=2))


if __name__ == '__main__':
    main()

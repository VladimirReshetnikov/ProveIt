"""Replay generic derived case, substitution, and native proof compilers."""
import json
from pathlib import Path
import subprocess
import sys
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'code'))
from transformations import *
from verify_mirror import build, accepts

HERE = Path(__file__).resolve().parent

def identity_closure(seed, n, context):
    matrix_seed = M.shift(seed, 2)
    matrix = Eq(matrix_seed, I(V(0), matrix_seed, V(0)))
    opened = M.sub(['q', matrix], Z)[1]
    branch_context = [opened] + [M.shift(a) for a in context]
    branch = Proofs(n + 1, branch_context)
    step = branch.sym(branch.ev(branch.sym(branch.hyp(0)), branch.refl(I(S(V(0)), M.shift(seed), V(0)))))
    major = ['di', matrix, Z, step]
    return ['de', ['q', opened], major, ['hyp', 0]]

def genuine_flip():
    matrix = Eq(V(2), I(V(0), V(3), V(0)))
    assert not guard(matrix)
    opened = M.sub(['q', matrix], Z)[1]
    base = M.shift(M.sub(opened, Z))
    branch = Proofs(3, [base])
    p_to_q = branch.trans(branch.hyp(0), branch.zero(V(2), V(0)))
    qclosure = identity_closure(V(2), 3, [base])
    qbase = branch.sym(branch.zero(V(2), V(0)))
    qtarget = ['qe', S(V(0)), qclosure, qbase]
    step = branch.trans(p_to_q, qtarget)
    source = Proofs(2).certificate(['di', matrix, Z, step])
    sigma = [V(0), V(0)]
    goal = substitute(source['goal'], sigma)
    assert guard(goal[1])
    uncorrected = {'variables': 1, 'context': [], 'goal': goal,
                   'proof': syntactic_substitution(source['proof'], sigma)}
    repaired = dict(uncorrected, proof=substitute_derivation(source['proof'], [], 2, sigma, 1))
    return source, uncorrected, repaired

def case_example():
    matrix = Eq(Z, I(V(0), Z, V(0)))
    base = M.shift(M.sub(matrix, Z))
    P = Proofs(1, [base])
    base_consumed = P.trans(P.hyp(0), P.zero(Z, V(0)))
    q = identity_closure(Z, 1, [base])
    target = ['qe', S(V(0)), q, P.sym(P.zero(Z, V(0)))]
    branch = P.trans(base_consumed, target)
    converted = case_di(matrix, Z, branch, [], 0)
    c = Proofs().certificate(converted)
    bad = dict(c, proof=['di', matrix, Z, branch])
    return c, bad

def main():
    destination = ROOT / 'examples' / 'transformed'
    destination.mkdir(parents=True, exist_ok=True)
    stats = {'native_replays': 0, 'numerical_substitution_replays': 0,
             'derived_case_replays': 0, 'guard_flip_replays': 0,
             'deliberately_unrepaired_rejections': 0, 'native_cli_replays': 0}
    source_set = [(name, c) for name, (c, good, _) in build().items() if good]
    source, broken, repaired = genuine_flip()
    M.check(source)
    M.check(repaired)
    assert not accepts(M, broken)
    stats['guard_flip_replays'] = 2
    stats['deliberately_unrepaired_rejections'] += 1
    for name, c in [('genuine_guard_flip_source', source), ('genuine_guard_flip_unrepaired', broken), ('genuine_guard_flip_repaired', repaired)]:
        (destination / (name + '.json')).write_text(json.dumps(c, indent=2) + '\n')
    source_set += [('genuine_guard_flip_source', source), ('genuine_guard_flip_repaired', repaired)]
    case, unrepaired_case = case_example()
    M.check(case)
    assert not accepts(M, unrepaired_case)
    stats['derived_case_replays'] = 1
    stats['deliberately_unrepaired_rejections'] += 1
    source_set.append(('derived_case_consumes_base', case))
    (destination / 'derived_case_consumes_base.json').write_text(json.dumps(case, indent=2) + '\n')

    for name, c in source_set:
        native = dict(c, proof=to_native(c['proof'], c['context'], c['variables']))
        N.check(native)
        stats['native_replays'] += 1
        path = destination / (name + '.native.json')
        path.write_text(json.dumps(native, indent=2) + '\n')
        for optimize in [False, True]:
            command = [sys.executable] + (['-O'] if optimize else []) + [str(ROOT / 'reference/native_checker.py')]
            result = subprocess.run(command, input=json.dumps(native), text=True, capture_output=True)
            assert result.returncode == 0 and result.stdout.strip() == 'ACCEPT', (name, optimize, result.stderr)
            stats['native_cli_replays'] += 1
        n = c['variables']
        substitutions = [([V(i) for i in range(n)], n),
                         ([V(i + 1) for i in range(n)], n + 1),
                         ([Z for _ in range(n)], 0),
                         ([I(Z, S(Z), V(0)) for _ in range(n)], 0)]
        for sigma, m in substitutions:
            converted = {'variables': m,
                         'context': [substitute(a, sigma) for a in c['context']],
                         'goal': substitute(c['goal'], sigma),
                         'proof': substitute_derivation(c['proof'], c['context'], n, sigma, m)}
            M.check(converted)
            stats['numerical_substitution_replays'] += 1

    stats['unexpected_outcomes'] = 0
    report = {'scope': 'Finite replays support implementations; the universal metatheorems require the written proofs.',
              'tests': stats,
              'reference_checker': 'Exact upstream diagonal_guard/code/native_checker.py at e1d9e3b12edd642ea2f5b572bb43febceaa50d93',
              'genuine_flip': 'B(x,y)=p=I(y,q;u.u), substitute p and q by the same variable; the old case proof actually consumes its zero-base assumption.',
              'derived_case': 'A mirrored matrix with an old case branch consuming its computationally reflexive zero base.'}
    (ROOT / 'evidence/transformation_verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()

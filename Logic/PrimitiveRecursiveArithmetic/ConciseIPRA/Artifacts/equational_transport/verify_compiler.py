"""Rebuild and replay proof translations. Run with ordinary Python 3.12.

The target checkers are also exercised as isolated processes with -O, so their
acceptance does not depend on assertions in this untrusted verification script.
"""
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'code'))
import source_liberal as C
import equation_back as E
import crossed_back as X
from compile_equational import compile_proof, clause_realizer, expand_legacy, rename, translate
from compile_crossed import convert


def check(condition, message):
    if not condition:
        raise AssertionError(message)


def count_nodes(proof):
    tag, *args = proof
    if tag == 'c':
        return 1
    if tag == 'u':
        return 1 + (count_nodes(args[-1]) if args[-1] is not None else 0)
    if tag in ('a', 'i'):
        return 1 + count_nodes(args[-1])
    return 1 + count_nodes(args[-1]) + count_nodes(args[-2])


def write_json(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, separators=(',', ':')) + '\n')


def run_checker(name, data, optimized, expected):
    command = [sys.executable, '-I', '-S'] + (['-O'] if optimized else [])
    command += [str(ROOT / 'code' / (name + '.py'))]
    run = subprocess.run(command, input=json.dumps(data), text=True,
                         capture_output=True, timeout=30)
    accepted = run.returncode == 0 and run.stdout == 'ACCEPT\n'
    check(accepted == expected, (name, optimized, expected, run.stdout, run.stderr))
    return dict(checker=name, optimized=optimized, expected=expected, accepted=accepted)


def family_formula(value, depth=1, diagonal=False):
    if diagonal:
        formula = [[[1, 1, value], [1, 1, 0]]]
    else:
        formula = [[[1, 0, value], 0]]
    for _ in range(depth - 1):
        formula = [formula]
    return formula


def main():
    started = time.monotonic()
    records = []
    processes = []
    sources = []
    for path in sorted((ROOT / 'reference' / 'legacy_control_fixtures').glob('*.json')):
        source = json.loads(path.read_text())
        source['proof'] = expand_legacy(source['proof'])
        sources.append((path.stem, source))
    # A genuinely non-vacuous Use at a supplied compound term: open a proof
    # of D_{x,y}(y=y), then specialize the clause y=y at S(S(0)).
    term = [0, [0, 0]]
    major = ['i', [[1, 1]], [0, 0],
             ['a', [0, -1], ['u', 1, 0, None]]]
    branch = ['u', 0, term, ['a', 0, ['u', 1, 0, None]]]
    sources.append(('arbitrary_compound_specialization',
                    {'goal': [term, term], 'proof': ['e', [term, term], major, branch]}))
    for case_name, source in sources:
        target = translate(source)
        crossed = {'goal': target['goal'], 'proof': convert(target['proof'])}
        X.verify(crossed)
        for label, data in [('source', source), ('equation', target), ('crossed', crossed)]:
            write_json(ROOT / 'tests' / label / (case_name + '.json'), data)
        for program, data in [('equation_back', target), ('crossed_back', crossed)]:
            for optimized in (False, True):
                processes.append(dict(case=case_name, **run_checker(program, data, optimized, True)))
        records.append(dict(case=case_name, source_nodes=count_nodes(source['proof']),
                            equation_nodes=count_nodes(target['proof']),
                            crossed_nodes=count_nodes(crossed['proof'])))

    # Full A_* source cases unavailable in the older witness-only compiler:
    # old (not newest) Back sources, arbitrary Use terms, and self-containing
    # replacement. Include both introduction modes and nested formula binders.
    open_records = []
    for self_occurring in (False, True):
        scope = 1 if self_occurring else 2
        source_parameter = -1
        replacement = [0, -1] if self_occurring else -2
        for depth in (1, 2, 3):
            for diagonal in (False, True):
                formula = lambda v: family_formula(v, depth, diagonal)
                context = [([], [source_parameter, replacement]),
                           ([], formula(replacement))]
                # The arbitrary specialization term is S(S(0)), deliberately
                # different from the newest source parameter.
                use = lambda index: ['u', index, [0, [0, 0]], None]
                proof = ['v', formula(source_parameter), use(0), use(1)]
                expected = C.derive(proof, context, scope)
                target = compile_proof(proof, context, scope)
                crossed = convert(target, context, scope)
                check(E.derive(target, context, scope) == expected, 'open equation target')
                check(X.derive(crossed, context, scope) == expected, 'open crossed target')
                case = f"open_self{int(self_occurring)}_depth{depth}_diag{int(diagonal)}"
                write_json(ROOT / 'tests' / 'open' / (case + '.json'),
                           dict(scope=scope, context=context, goal=expected,
                                source_proof=proof, equation_proof=target, crossed_proof=crossed))
                open_records.append(dict(case=case, equation_nodes=count_nodes(target),
                                         crossed_nodes=count_nodes(crossed)))

    # A non-order-preserving injection and a noncontiguous clause placement.
    source_context = [([], [-1, -2]), ([], family_formula(-2, 2))]
    proof = ['v', family_formula(-1, 2), ['u', 0, 0, None], ['u', 1, 0, None]]
    mapping = {-1: -3, -2: -1}
    mapped = [(rename(a, mapping), rename(b, mapping)) for a, b in source_context]
    receiving = [([], [0, 0]), mapped[0], ([], [[0, 0], [0, 0]]), mapped[1]]
    target = compile_proof(proof, source_context, 2, receiving, 4, mapping,
                           [clause_realizer(1), clause_realizer(3)])
    expected = family_formula(-3, 2)
    check(E.derive(target, receiving, 4) == expected, 'nonmonotone injection')
    check(X.derive(convert(target, receiving, 4), receiving, 4) == expected, 'crossed nonmonotone injection')
    write_json(ROOT / 'tests' / 'open' / 'nonmonotone_embedding.json',
               dict(scope=4, context=receiving, goal=expected,
                    equation_proof=target, crossed_proof=convert(target, receiving, 4)))
    open_records.append(dict(case='nonmonotone_embedding', equation_nodes=count_nodes(target),
                             crossed_nodes=count_nodes(convert(target, receiving, 4))))

    # An unused premise is outside the rule-directed validation contract.
    # The crossed converter must drop it rather than trying to compile it.
    ignored = {'goal': [0, 0], 'proof': ['a', 0, ['u', 0, ['unused', {'ignored': True}]]]}
    E.verify(ignored)
    repaired = {'goal': ignored['goal'], 'proof': convert(ignored['proof'])}
    X.verify(repaired)
    write_json(ROOT / 'tests' / 'crossed' / 'ignored_use_payload.json', repaired)
    for optimized in (False, True):
        processes.append(dict(case='ignored_use_payload',
                              **run_checker('crossed_back', repaired, optimized, True)))

    for path in sorted((ROOT / 'reference' / 'legacy_adversarial').glob('*.json')):
        data = json.loads(path.read_text())
        for program in ('equation_back', 'crossed_back'):
            for optimized in (False, True):
                processes.append(dict(case=path.stem, **run_checker(program, data, optimized, False)))

    receipt = dict(closed_translations=len(records), open_translations=len(open_records),
                   subprocess_runs=len(processes), failures=0, seconds=round(time.monotonic()-started, 3),
                   closed=records, open=open_records, processes=processes,
                   limitation='Executable proof witnesses and finite regressions; not a Lean/Rocq formalization or an exhaustive proof-checker verification.')
    (ROOT / 'evidence' / 'compiler_validation.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k:v for k,v in receipt.items() if k not in ('closed','open','processes')}, indent=2))


if __name__ == '__main__':
    main()

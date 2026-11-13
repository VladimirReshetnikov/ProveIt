"""Focused executable checks of the new rule and structural compiler.

These finite tests are regression evidence, not a proof of all executions.
Run from this directory with Python 3.12 or later.
"""
import ast
import hashlib
import io
import json
from pathlib import Path
import platform
import tokenize

import checker as target
import control_liberal as source
import control_newest_close as baseline
import proof_tools as p
from translate import translate

ROOT = Path(__file__).resolve().parent
results = []


def accept(name, proof, expected, context=p.INITIAL):
    actual = target.prove(proof, context)
    assert actual == expected, (name, actual, expected)
    results.append({'name': name, 'kind': 'accept', 'passed': True})


def reject(name, thunk):
    try:
        thunk()
    except (ValueError, TypeError, IndexError, RecursionError):
        results.append({'name': name, 'kind': 'reject', 'passed': True})
        return
    raise AssertionError('unexpected acceptance: ' + name)


def compile_case(name, proof, source_context=p.INITIAL,
                 target_context=p.INITIAL, numerical=None, clauses=None):
    old = source.prove(proof, source_context)
    out = translate(proof, source_context, target_context, numerical, clauses)
    expected = old if numerical is None else target.walk(
        old, lambda i, d: numerical[i] if i < 0 else i)
    accept(name, out, expected, target_context)
    return out


def metrics(path):
    tree = ast.parse(path.read_text())
    normalized = ast.unparse(tree) + '\n'
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
               tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    return {'file': path.name,
            'tokens': sum(t.type not in ignored for t in tokenize.generate_tokens(
                io.StringIO(normalized).readline)),
            'ast_nodes': sum(1 for _ in ast.walk(tree)),
            'normalized_bytes': len(normalized.encode('utf-8')),
            'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def main():
    numerals = [0]
    for _ in range(5):
        numerals.append(p.S(numerals[-1]))
    for n, term in enumerate(numerals):
        accept('vacuous_packet_' + str(n), p.vacuous(term, p.INITIAL), [[2, term]])
        accept('arbitrary_reflexivity_' + str(n), p.refl(p.INITIAL, term), [term, term])

    # Actual nontrivial conditional-copy helpers, not only vacuous packets.
    for depth, H in enumerate([[p.V, p.ONE], [[p.V, p.V]], [[[p.V, p.ONE]]]]):
        accept('conditional_copy_depth_' + str(depth),
               p.delta_proof(p.TWO, H), p.delta(p.TWO, H))

    simple = [[0, 0, None], [0, p.TWO, None],
              [[2, p.ONE], p.ONE, [0, p.ONE, None]],
              [[2, 2], p.TWO, [0, p.TWO, None]],
              [[2, 2], 0, [0, 0, None]]]
    for n, proof in enumerate(simple):
        compile_case('liberal_translation_' + str(n), proof)

    existential = p.D(p.gate(p.Y, [p.X, p.ONE]))
    compile_case('existential_witness_one',
                 [existential[0], p.ONE, [0, p.ONE, None]])
    identity_iteration = p.P([p.Y, 0, p.S(p.P(1))])
    induction = p.D([identity_iteration, 0])
    compile_case('identity_iteration_with_used_induction_hypothesis',
                 [induction[0], 0, [1, 0, None]])

    # A Use antecedent containing Close must be rebuilt after the new
    # specialization parameter is added.  A literal weakening would fail.
    A = [[2, p.ONE]]
    old_context = p.INITIAL + [(A, [1, 1])]
    premise = [[2, p.ONE], p.ONE, [0, p.ONE, None]]
    critical = [1, p.TWO, premise]
    compile_case('antecedent_close_rebuilt_under_newest', critical, old_context,
                 old_context)

    # Explicit nontrivial parameter injection, extra target clauses, and
    # a source witness no longer mapped to the newest target parameter.
    old_context = p.INITIAL + [([], [-1, -1])]
    enlarged = p.INITIAL + [([], [0, 0]), ([], [-2, -2]), ([], [0, 0])]
    embedded = [[2, -1], -1, [1, 0, None]]
    compile_case('scope_and_clause_embedding', embedded, old_context, enlarged,
                 {-1: -2}, [0, 2])

    # The old selector's 0/1 packet is retained.  Its second positive row
    # carries a different equation, so a successor-row-only selector
    # would not be a replacement for this test.
    packet = p.D(p.gate(p.Y, [p.C(p.P(p.Y), p.X, p.S(p.X)),
                             p.C(p.P(p.Y), p.ONE, p.TWO)]))
    body = source.sub(packet[0], p.ONE, 1)
    step = source.sub(body, p.S(-1))
    assert len(step) == 2 and step[0] == step[1]
    major = [packet[0], p.ONE, [0, step[0], None]]
    old_export = [[], major, [1, p.TWO, [0, 0, None]]]
    compile_case('old_transport_packet_selector', old_export)

    # The new override changes the selector on a source Export, but the
    # old fallback required its branch output to be independent of b.
    for name, matrix in [('constant', [2, p.ONE]),
                         ('self_dependent', [2, p.S(2)])]:
        major = [matrix, 0, [1, 0, None]]
        compile_case('old_export_override_' + name,
                     [[], major, [0, 0, None]])

    # Direct test of r(b) containing b: a b-free branch is sound and
    # accepted; a branch still mentioning b after substitution rejects.
    self_major = [[2, p.S(2)], [1, None]]
    opened = p.INITIAL + [([-1, p.S(-1)], [-1, p.S(-1)])]
    accept('self_dependent_vacuous_bfree_export',
           [[], self_major, p.refl(opened, 0)], [0, 0])
    neutral = [-1, 0, 0]
    accept('self_dependent_replacement_erased_by_normalization',
           [[], self_major, p.refl(opened, neutral)], [0, 0])
    reject('self_dependent_vacuous_scope_escape',
           lambda: target.prove([[], self_major, [0, None]], p.INITIAL))

    # Rows 0 and 1 may agree without the entire body being constant.
    # The implementation tests B == sub(B,0), not merely row0 == row1.
    f = p.C(p.Y, 0, p.C(p.P(p.Y), 0, p.ONE))
    dependent = p.D([p.X, f])
    context = p.INITIAL + [([], dependent)]
    reject('equal_first_two_rows_do_not_imply_vacuity',
           lambda: target.prove([[], [1, None], [0, None]], context))

    reject('unproved_contradiction', lambda: target.check([[0, p.ONE], [0, None]]))
    reject('boolean_goal_alias', lambda: target.check([[False, False], [0, None]]))
    reject('float_goal_alias', lambda: target.check([[0.0, 0.0], [0, None]]))
    reject('negative_clause_index', lambda: target.prove([-1, None], p.INITIAL))
    reject('future_clause_index', lambda: target.prove([1, None], p.INITIAL))
    reject('old_use_packet_not_new_format',
           lambda: target.prove([0, 0, None], p.INITIAL))
    reject('future_parameter_in_packet',
           lambda: target.prove([[2, -10], [1, None]], p.INITIAL))
    reject('ill_sorted_formula', lambda: target.prove([[0, 0, 0], [1, None]], p.INITIAL))

    evidence = {'python': platform.python_version(),
                'checks': len(results), 'passed': sum(x['passed'] for x in results),
                'universal_proof': False, 'results': results,
                'metrics': [metrics(ROOT / 'control_newest_close.py'),
                            metrics(ROOT / 'checker.py')]}
    (ROOT / 'evidence.json').write_text(json.dumps(evidence, indent=2) + '\n')
    print(json.dumps(evidence, indent=2))


if __name__ == '__main__':
    main()

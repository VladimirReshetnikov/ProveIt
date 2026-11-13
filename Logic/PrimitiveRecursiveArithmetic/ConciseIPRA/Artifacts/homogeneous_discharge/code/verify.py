"""Reproduce sizes and exercise rules, deep gates, compilers, and rejections."""
import ast
import copy
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

import h4_checker as h4
import h3_checker as h3
import h4_seed_checker as h4s
import h3_seed_checker as h3s
from translations import fuse, separate, truth, weaken, explicit_bases


def refl(t):
    return ['use', 0, t, None]


def zero(s, h=0):
    return ['eval', refl(s), refl([0, s, h])]


def succ(c, a, h):
    return ['eval', refl([c, a, h]), refl([[c], a, h])]


def compose(e, f, n, context):
    """From proofs s=t and s=r, obtain r=t using only zero evaluations."""
    s, _ = h4.check(e, n, context)
    assert h4.check(f, n, context)[0] == s
    frame = [0, s, 0]
    return ['eval', e, ['eval', f, refl(frame)]]


def sym(e, n, context):
    s, _ = h4.check(e, n, context)
    return compose(refl(s), e, n, context)


def trans(e, f, n, context):
    assert h4.check(e, n, context)[1] == h4.check(f, n, context)[0]
    return compose(f, sym(e, n, context), n, context)


def deep_refl(a, n=0, context=None):
    if context is None:
        context = [[1, 1]]
    assert h4.reflexive(a)
    if len(a) == 2:
        return refl(a[0])
    b = a[0]
    seed = h4.instance(b, [int(h4.diagonal(b)), 0], True, 1)
    target = h4.instance(b, [[1], 0], True, 1)
    ext = h4.branch_context(context, h4.gate(seed))
    return ['intro', a, 0, deep_refl(target, n + 1, ext)]


def gate_access_atomic(a, context, n=0, index=None):
    """Recover a raw equation from its one-body gate assumption."""
    if index is None:
        index = len(context) - 1
    s, t = a
    e = ['use', index, [0], None]
    assert h4.check(e, n, context) == h4.instance(h4.gate(a), [[0]], True)
    k = [0, s, h4.lift(t)]
    j = [[0], s, h4.lift(t)]
    k_to_s = zero(s, h4.lift(t))
    j_to_t = succ(0, s, h4.lift(t))
    assert h4.check(k_to_s, n, context) == [k, s]
    assert h4.check(j_to_t, n, context) == [j, t]
    s_to_j = compose(e, k_to_s, n, context)
    return trans(s_to_j, j_to_t, n, context)


def score(path):
    normalized = ast.unparse(ast.parse(path.read_text())) + '\n'
    ignored = {tokenize.ENCODING, tokenize.NL, tokenize.NEWLINE,
               tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER,
               tokenize.COMMENT}
    tokens = sum(t.type not in ignored for t in
                 tokenize.generate_tokens(io.StringIO(normalized).readline))
    return {'tokens': tokens, 'ast_nodes': sum(1 for _ in ast.walk(ast.parse(normalized))),
            'normalized_bytes': len(normalized.encode())}


def main():
    root = Path(__file__).parent
    samples = {
        'reflexivity': refl([0]),
        'compound_truth': truth(),
        'zero_computation': zero([0], [1]),
        'successor_computation': succ([0], 0, [1]),
        'deep_reflexivity': deep_refl([[[1, 1]]]),
        'diagonal_introduction': deep_refl([[[1, 1, 0], [1, 1, 0]]]),
        'open_clause': ['open', ['intro', [[1, 1]], 0, refl([1])],
                        ['use', 1, [0], None]],
    }
    reports = []
    for name, p in samples.items():
        goal = h4.check(p)
        q = fuse(p)
        assert h4.accepts([goal, p]), name
        assert h3.accepts([goal, q]), name
        assert h4.accepts([goal, separate(q)]), name
        seeded = explicit_bases(p)
        assert h4s.accepts([goal, seeded]), name
        fused_seeded = fuse(seeded)
        assert h3s.accepts([goal, fused_seeded]), name
        assert h4s.accepts([goal, separate(fused_seeded)]), name
        reports.append(name)
        (root / (name + '.h3.json')).write_text(json.dumps([goal, q], separators=(',', ':')) + '\n')
        (root / (name + '.h3_seed.json')).write_text(json.dumps([goal, fused_seeded], separators=(',', ':')) + '\n')

    # Actual recovery of an arbitrary equation with two free parameters from its gate.
    # The equation is not true in the empty context. Both sides are nontrivial terms.
    a = [[1], [2, 0, [1]]]
    context = [[1, 1], h4.gate(a)]
    p = gate_access_atomic(a, context, n=2)
    assert h4.check(p, 2, context) == a
    q = fuse(p, len(context))
    assert h3.check(q, 2, context) == a
    assert h4.check(separate(q, 2, context), 2, context) == a
    p_seeded = explicit_bases(p, 2, context)
    q_seeded = fuse(p_seeded, len(context))
    assert h4s.check(p_seeded, 2, context) == a
    assert h3s.check(q_seeded, 2, context) == a
    assert h4s.check(separate(q_seeded, 2, context), 2, context) == a
    reports.append('atomic_gate_access_with_free_parameters')

    # The compiler must move the clause index after an inserted scope, including
    # inside subsequent introductions, rather than lifting all variables blindly.
    nested = ['open', truth(), ['intro', [[0, 0]], 0, refl(0)]]
    g = h4.check(nested)
    assert h3.accepts([g, fuse(nested)])
    assert h3s.accepts([g, fuse(explicit_bases(nested))])
    reports.append('nested_scope_translation')

    # A source Use with a deep reflexive base is expanded to an actual proof;
    # the final checker contains no recursive reflexivity predicate.
    deep_body = [[[1, 1]]]
    deep_major = [deep_body]
    source = ['open', deep_refl(deep_major), ['use', 1, 0, None]]
    deep_goal = h4.check(source)
    explicit = explicit_bases(source)
    assert h4s.accepts([deep_goal, explicit])
    assert h3s.accepts([deep_goal, fuse(explicit)])
    reports.append('deep_omitted_base_expansion')

    omitted = [[0, 0], ['discharge', truth(), truth(), ['use', 1, 0, None]]]
    assert h3.accepts(omitted)
    assert not h3s.accepts(omitted)
    supplied = copy.deepcopy(omitted)
    supplied[1][3][3] = refl(0)
    assert h3s.accepts(supplied)
    reports.append('only_fixed_seed_allows_omission')

    invalid = {
        'false_goal': [[0, [0]], refl(0)],
        'boolean_variable': [[0, 0], ['use', 0, True, None]],
        'out_of_scope_variable': [[1, 1], refl(1)],
        'negative_clause': [[0, 0], ['use', -1, 0, None]],
        'unproved_base': [[0, 0], ['use', 1, 0, None]],
        'eigenvariable_escape': [[0, 0], ['discharge', truth(), truth(), refl(1)]],
        'arithmetic_mismatch': [[0, 0], ['discharge', truth(), refl(0), refl([0])]],
        'wrong_intro_step': [[[0, [0]]], ['intro', [[0, [0]]], 0, refl(0)]],
        'unknown_rule': [[0, 0], ['oracle', [0, 0]]],
    }
    for name, doc in invalid.items():
        assert not h3.accepts(doc), name
        assert not h3s.accepts(doc), name
    (root / 'negative_cases.json').write_text(json.dumps(invalid, indent=2) + '\n')
    optimized = []
    for name in ('h4_checker.py', 'h3_checker.py', 'h4_seed_checker.py', 'h3_seed_checker.py'):
        for mode in ('-O', '-OO'):
            run = subprocess.run([sys.executable, mode, str(root / name)],
                                 input=json.dumps([[0, 0], refl(0)]),
                                 text=True, capture_output=True)
            assert run.returncode != 0 and not run.stdout.strip(), (name, mode)
            assert 'Run this checker without -O' in run.stderr, (name, mode)
            optimized.append(name + ':' + mode)
    result = {'python_version': sys.version.split()[0],
              'h4': score(root / 'h4_checker.py'),
              'h3': score(root / 'h3_checker.py'),
              'h4_seed': score(root / 'h4_seed_checker.py'),
              'h3_seed': score(root / 'h3_seed_checker.py'),
              'positive_checks': reports,
              'negative_checks': sorted(invalid),
              'optimized_modes_rejected': optimized,
              'scope': 'Executable regression checks; the general equivalence is a written proof.',
              'global_record_claim': False}
    (root / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()

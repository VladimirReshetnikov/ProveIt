"""Reproduce matched sizes and replay the untrusted bidirectional compiler."""
import ast
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

from translate import from_upstream, to_newest, to_reference, name_matrix

HERE = Path(__file__).resolve().parent


def load_checker(path):
    module = ast.parse(path.read_text())
    definitions = ast.Module(body=module.body[:-3], type_ignores=[])
    namespace = {}
    exec(compile(definitions, str(path), 'exec'), namespace)
    return namespace


REFERENCE = load_checker(HERE / 'checkers/reference.py')
NEWEST = load_checker(HERE / 'checkers/newest.py')
CLAUSAL = load_checker(HERE / 'checkers/newest_reflexive_clause.py')


def check(which, goal, proof, context=None):
    try:
        which['prove'](goal, proof, [] if context is None else context)
    except (ValueError, TypeError, IndexError, RecursionError, AssertionError):
        return False
    return True


def command_replay(script, data):
    result = subprocess.run([sys.executable, '-I', '-S', '-B', str(script)],
                            input=json.dumps(data), text=True, capture_output=True)
    assert result.returncode == 0 and result.stdout == 'ACCEPT\n', result.stderr


def metrics(path):
    source = ast.unparse(ast.parse(path.read_text())) + '\n'
    ignore = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
              tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    return {'significant_tokens': sum(t.type not in ignore for t in
            tokenize.generate_tokens(io.StringIO(source).readline)),
            'ast_nodes': sum(1 for _ in ast.walk(ast.parse(source))),
            'normalized_bytes': len(source.encode()),
            'source_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def encode_reflexivity_clause(proof):
    if not proof:
        return []
    tag = proof[0]
    if tag == 'r':
        return ['u', 0, []]
    if tag == 'u':
        return ['u', proof[1] + 1, encode_reflexivity_clause(proof[2])]
    if tag == 'i':
        return ['i', proof[1], encode_reflexivity_clause(proof[2])]
    if tag == 'e':
        return ['e', proof[1], proof[2], encode_reflexivity_clause(proof[3]),
                encode_reflexivity_clause(proof[4])]
    raise ValueError('proof tag')


def main():
    accepted = []
    tests = HERE / 'tests'
    tests.mkdir(exist_ok=True)
    upstream = HERE / 'fixtures/source'
    for path in sorted(upstream.glob('*.json')):
        goal, proof = json.loads(path.read_text())
        proof = from_upstream(proof)
        assert check(REFERENCE, goal, proof), path.name
        translated = to_newest(goal, proof)
        assert check(NEWEST, goal, translated), path.name
        reverse = to_reference(goal, translated)
        assert check(REFERENCE, goal, reverse), path.name
        encoded = encode_reflexivity_clause(translated)
        assert check(CLAUSAL, goal, encoded, [([], [1, 1])]), path.name
        command_replay(HERE / 'checkers/newest_reflexive_clause.py', [goal, encoded])
        (tests / ('compact_' + path.name)).write_text(json.dumps([goal, encoded], separators=(',', ':')) + '\n')
        output = [goal, translated]
        (tests / path.name).write_text(json.dumps(output, separators=(',', ':')) + '\n')
        command_replay(HERE / 'checkers/newest.py', output)
        command_replay(HERE / 'checkers/reference.py', [goal, proof])
        accepted.append(path.stem)

    # Open sequent: one older free parameter and one conditional clause.
    # Its row at 0 is 0=0; arbitrary targets test regenerated premise proofs.
    context = [([0, 0], [[1, 0, -1], [1, 0, -1]])]
    targets = [0, [0, 0], -1, [0, -1], [-1, 0, [0, 1]]]
    open_cases = []
    for t in targets:
        goal = REFERENCE['sub'](context[0][1], t)
        proof = ['u', 0, t, ['r']]
        assert check(REFERENCE, goal, proof, context)
        translated = to_newest(goal, proof, context, context, {-1: -1}, [0])
        assert check(NEWEST, goal, translated, context)
        assert check(REFERENCE, goal, to_reference(goal, translated, context), context)
        open_cases.append({'goal': goal, 'reference_proof': proof,
                           'newest_proof': translated})

    # Capture regression: the clause target is used below two D binders
    # and the substituted neutral iterator has its own bound state variable.
    compound_context = [([0, 0], [[[1, 3, [0, 1]], [1, 3, [0, 1]]]])]
    neutral = [-1, 0, [0, 1]]
    compound_goal = REFERENCE['sub'](compound_context[0][1], neutral)
    compound_proof = ['u', 0, neutral, ['r']]
    assert check(REFERENCE, compound_goal, compound_proof, compound_context)
    compound_new = to_newest(compound_goal, compound_proof, compound_context,
                             compound_context, {-1: -1}, [0])
    assert check(NEWEST, compound_goal, compound_new, compound_context)
    assert check(REFERENCE, compound_goal, to_reference(compound_goal, compound_new,
                                                       compound_context), compound_context)

    # Nontrivial renaming and a nonterminal context embedding: the new scope
    # contains an extra clause before the source clause and one after it.
    extra = ([], [0, 0])
    target_context = [extra,
            ([0, 0], [[1, 0, -2], [1, 0, -2]]), extra]
    source_goal = [[0, -1], [0, -1]]
    source_context = [([], [1, 1])]
    source_proof = ['u', 0, [0, -1], []]
    assert check(REFERENCE, source_goal, source_proof, source_context)
    target_context = [extra, ([], [1, 1]), extra]
    translated = to_newest(source_goal, source_proof, source_context,
                           target_context, {-1: -2}, [1])
    renamed_goal = [[0, -2], [0, -2]]
    assert check(NEWEST, renamed_goal, translated, target_context)

    rejected = {
        'false_reflexivity': ([[0, 0], 0], ['r']),
        'free_root_variable': ([-1, -1], ['r']),
        'loose_bound_index': ([1, 1], ['r']),
        'boolean_zero': ([False, False], ['r']),
        'missing_clause': ([0, 0], ['u', 0, []]),
        'negative_clause': ([0, 0], ['u', -1, []]),
        'extra_target_field': ([0, 0], ['u', 0, 0, []]),
        'fresh_witness_in_major': ([name_matrix(-1)], ['i', -1, ['r']]),
        'invalid_erased_body': ([[0, 0, 999], [0, 0, 999]], ['r']),
        'non_normal_reflexivity': ([[0, 0, 0], [0, 0, 0]], ['r']),
        'invalid_successor_tag': ([[7, 0], [7, 0]], ['r']),
    }
    for name, (goal, proof) in rejected.items():
        assert not check(NEWEST, goal, proof), name
    # The candidate must reject an unavailable future level under a scope.
    assert not check(NEWEST, [-2, -2], ['r'], [extra])
    # A failed name test cannot export an unproved equation at 0=1.
    bad_matrix = [[1, 0, 0], [1, 0, [0, 0]]]
    assert not check(NEWEST, [0, [0, 0]],
                     ['e', bad_matrix, [-1, [0, 0]], ['i', 0, ['r']], ['r']])
    # The compact protocol must retain independent Intro witness validation.
    # Its naming matrix may ignore x, so a malformed witness can otherwise
    # disappear before any term traversal reaches it.
    malformed_witnesses = [-1, 1, False, [0, 0, 999], [0, 0, 0], [7, 0]]
    for witness in malformed_witnesses:
        assert not check(CLAUSAL, [[0, 0]],
                         ['i', witness, ['u', 0, []]], [([], [1, 1])]), witness
        assert not check(NEWEST, [[0, 0]], ['i', witness, ['r']]), witness
    assert not check(CLAUSAL, [[0, 0], 0], ['u', 0, []], [([], [1, 1])])
    (tests / 'malformed_intro_witnesses.json').write_text(
        json.dumps([[[[0, 0]], ['i', t, ['u', 0, []]]] for t in malformed_witnesses],
                   indent=2) + '\n')
    (tests / 'open_context_cases.json').write_text(json.dumps(open_cases, indent=2) + '\n')
    result = {
        'python_version': sys.version.split()[0],
        'reference': metrics(HERE / 'checkers/reference.py'),
        'newest': metrics(HERE / 'checkers/newest.py'),
        'reference_clause': metrics(HERE / 'checkers/reference_clause.py'),
        'newest_reflexive_clause': metrics(HERE / 'checkers/newest_reflexive_clause.py'),
        'closed_bidirectional_fixtures': accepted,
        'closed_fixtures': len(accepted),
        'open_context_targets': len(open_cases),
        'nontrivial_renaming_and_context_embedding': True,
        'capture_below_formula_and_iterator_binders': True,
        'negative_controls': len(rejected) + 2,
        'compact_intro_witness_negative_controls': len(malformed_witnesses),
        'compact_false_reflexivity_rejected': True,
        'formalized_in_lean': False,
        'meaning': 'Executable finite checks supplement the written all-sequent theorem.'}
    (HERE / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()

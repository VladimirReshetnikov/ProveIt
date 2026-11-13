"""Reproduce the shifted shared-leaf comparison, without network access."""
from pathlib import Path
import ast
import hashlib
import io
import json
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.COMMENT,
        tokenize.NEWLINE, tokenize.NL, tokenize.INDENT, tokenize.DEDENT}
CHANGES = [('d=0:', 'd=2:'), ('d=3)', 'd=5)'),
           ('i(t, [s, u, t], 3)', 'i(t, [s, u, t], 5)'),
           ('i(*a, t, 2)', 'i(*a, t, 4)'),
           ('c([[]], *q())', 'c([0], *q())')]


def normalized(source):
    return ast.unparse(ast.parse(source)) + '\n'


def metrics(path):
    text = normalized(path.read_text())
    return dict(file=path.name,
                tokens=sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(text).readline)),
                ast_nodes=len(list(ast.walk(ast.parse(text)))),
                normalized_bytes=len(text.encode()),
                sha256=hashlib.sha256(path.read_bytes()).hexdigest())


def shift(tree):
    if type(tree) is list:
        return [shift(child) for child in tree]
    return tree + 2 if type(tree) is int and tree > 0 else tree


def translate(data):
    """Coordinate translation for the documented canonical certificate subset.

    This producer is untrusted. It is not a validator for arbitrary JSON and
    does not promise equivalence on noncanonical aliases.
    """
    result = shift(data)
    for packet in result[:-1]:
        if type(packet) is list and len(packet) == 4 and packet[0] == []:
            packet[0] = 0
    return result


def execute(program, data, optimized):
    command = [sys.executable, '-I', '-S', '-B']
    if optimized:
        command.append('-O')
    command.append(str(ROOT / program))
    result = subprocess.run(command, input=json.dumps(data).encode(),
                            capture_output=True, timeout=10)
    return result.returncode == 0 and result.stdout == b'ACCEPT\n'


def main():
    expected_source = (ROOT / 'control469.py').read_text()
    for before, after in CHANGES:
        if expected_source.count(before) != 1:
            raise ValueError(('unexpected source', before))
        expected_source = expected_source.replace(before, after)
    if (ROOT / 'checker468.py').read_text() != normalized(expected_source):
        raise ValueError('Candidate differs from declared five edits')

    rows = []
    for path in sorted((ROOT / 'fixtures_original').glob('*.json')):
        original = json.loads(path.read_bytes())
        accepted = not path.name.startswith(('reject_', 'future_witness'))
        cases = [(path.name, original, accepted)]
        if accepted:
            bad = json.loads(path.read_bytes())
            bad[-1] = [[0, [0]], 0]
            cases.append(('false_' + path.name, bad, False))
        for name, data, expected in cases:
            shifted = translate(data)
            fixture = ROOT / 'fixtures468' / name
            if json.loads(fixture.read_bytes()) != shifted:
                raise ValueError(('unexpected translated fixture', name))
            for program, payload in [('control469.py', data), ('checker468.py', shifted)]:
                for optimized in [False, True]:
                    actual = execute(program, payload, optimized)
                    rows.append(dict(case=name, program=program, optimized=optimized,
                                     expected=expected, accepted=actual, passed=actual == expected))
    # These are new-code semantic tests, deliberately outside a claim of raw
    # trace conjugacy. Their PUBLIC goal remains canonical. The noncanonical
    # coordinates occur only in an auxiliary computation major.
    goal = [[0, [0], 0], [0]]
    auxiliaries = []
    for alias in [1, 2, 3, 4, 5, -1]:
        major = [[0, alias, 0], alias]
        data = [[0, 0, [0], 0], [0, 0, alias, 0],
                [major, 0, 0, 0], [goal, 0]]
        auxiliaries.append(('aux_alias_' + str(alias), data, 1 <= alias <= 4))
    data = [[0, 0, [0], 0], [0, 0, 0, 0], [0, 0, 0, 0],
            [0, 0, 0, 0], [[[0, 0, 0, 0]], 0, 0, 0], [goal, 0]]
    auxiliaries.append(('aux_neutral_arity_four', data, True))
    for name, data, expected in auxiliaries:
        if json.loads((ROOT / 'fixtures468' / (name + '.json')).read_bytes()) != data:
            raise ValueError(('unexpected auxiliary fixture', name))
        cases = [(name, data, expected)]
        if expected:
            bad = json.loads(json.dumps(data))
            bad[-1] = [[0, [0]], 0]
            cases.append(('false_' + name, bad, False))
        for case_name, payload, outcome in cases:
            for optimized in [False, True]:
                actual = execute('checker468.py', payload, optimized)
                rows.append(dict(case=case_name, program='checker468.py', optimized=optimized,
                                 expected=outcome, accepted=actual, passed=actual == outcome))
    failures = [row for row in rows if not row['passed']]
    report = dict(python=sys.version, exact_source_edits=CHANGES,
                  metrics=[metrics(ROOT / name) for name in ['control469.py', 'checker468.py']],
                  checks=len(rows), failed=failures, results=rows)
    (ROOT / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({key: value for key, value in report.items() if key != 'results'}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()

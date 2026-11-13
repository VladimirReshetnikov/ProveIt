"""Reproduce canonical translations and isolated executable checks.

The checkers import none of this validation code. This finite experiment does
not establish the universal soundness/completeness theorem.
"""
from collections import Counter
from hashlib import sha256
from pathlib import Path
import ast
import io
import json
import platform
import subprocess
import sys
import tokenize

from translate import Translation, read_stream, write_stream, integerize

ROOT = Path(__file__).resolve().parent
CHECKER = ROOT / 'checker_opaque_stream.py'
CONTROL = ROOT / 'controls/checker_tokens239.py'
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def measure(path):
    source = path.read_bytes()
    normalized = (ast.unparse(ast.parse(source)) + '\n').encode()
    return dict(path=str(path.relative_to(ROOT)),
                significant_tokens=sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)),
                ast_nodes=len(list(ast.walk(ast.parse(normalized)))),
                normalized_bytes=len(normalized),
                sha256=sha256(source).hexdigest(),
                normalized_sha256=sha256(normalized).hexdigest())


def execute(checker, data, optimized, label, expected):
    command = [sys.executable, '-I', '-S', '-B']
    if optimized:
        command.append('-O')
    command.append(str(checker))
    process = subprocess.run(command, input=data, capture_output=True, timeout=30)
    accepted = process.returncode == 0 and process.stdout == b'ACCEPT\n'
    return dict(checker=str(checker.relative_to(ROOT)), fixture=label,
                optimized=optimized, expected=expected, accepted=accepted,
                exit_code=process.returncode,
                error=process.stderr.decode(errors='replace').splitlines()[-1:] if process.stderr else [])


def stream_bytes(rows):
    return ''.join(json.dumps(integerize(row), separators=(',', ':')) + '\n' for row in rows).encode()


def main():
    executions = []
    translations = []
    for source in sorted((ROOT / 'source_fixtures').glob('*.jsonl')):
        rows = read_stream(source)
        translation = Translation(rows)
        output = translation.run()
        target = ROOT / 'fixtures' / source.name
        write_stream(target, output)
        translations.append(dict(name=source.name,
                                 source_sha256=sha256(source.read_bytes()).hexdigest(),
                                 target_sha256=sha256(target.read_bytes()).hexdigest(),
                                 packets=translation.cursor - 1,
                                 target_bytes=target.stat().st_size,
                                 allocations=translation.allocations,
                                 rule_events=dict(Counter(e['rule'] for e in translation.events))))
        for optimized in (False, True):
            executions.append(execute(CONTROL, source.read_bytes(), optimized, source.name, True))
            executions.append(execute(CHECKER, target.read_bytes(), optimized, source.name, True))
            # The root has no free parameters and this equation is false in N.
            altered = [[0, [0]], *output[1:]]
            executions.append(execute(CHECKER, stream_bytes(altered), optimized,
                                      'false_root__' + source.name, False))

    for negative in sorted((ROOT / 'negative').glob('*.jsonl')):
        for optimized in (False, True):
            executions.append(execute(CHECKER, negative.read_bytes(), optimized,
                                      negative.name, False))
    for optimized in (False, True):
        executions.append(execute(ROOT / 'negative/deliberately_unsound_fixed_name.py',
                                  (ROOT / 'negative/fixed_name_capture.jsonl').read_bytes(),
                                  optimized, 'fixed_name_capture.jsonl', True))

    # Opaque labels include apparent exposed slots and nested trees. They are
    # variables, so neither depth nor the supplied image may alter them.
    t = Translation([[0, 0]])
    names = [[0, 0, 0, 0], [[], [100], [-200], [[3]], 999],
             [[0, 0, 0, 0], [], [], [[], [], [], []]]]
    fixed_points = 0
    for name in names:
        for depth in range(-20, 21):
            for image in (0, [0], [3], [[], [], [], []]):
                assert t.new_open(name, image, depth) is name
                fixed_points += 1

    failures = [e for e in executions if e['accepted'] != e['expected']]
    receipt = dict(python=platform.python_version(),
                   source_repository='VladimirReshetnikov/ProveIt',
                   source_commit='fc05b10f0e03f22edbfdde9298a29fb2fee5dc59',
                   scope='selected canonical fixtures only; no arbitrary-raw-input equivalence claim',
                   metrics=[measure(CONTROL), measure(CHECKER)],
                   translations=translations,
                   opaque_fixed_point_checks=fixed_points,
                   executions=executions,
                   execution_count=len(executions), failures=failures)
    (ROOT / 'verification_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(dict(translations=len(translations), executions=len(executions),
                          fixed_point_checks=fixed_points, failed_expectations=len(failures),
                          metrics=receipt['metrics']), indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()

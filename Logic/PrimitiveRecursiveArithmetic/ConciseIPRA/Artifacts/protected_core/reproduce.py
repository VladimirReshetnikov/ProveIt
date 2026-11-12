"""Reproduce the protected-core certificates, audits, measurements and checks.

Run with Python 3.12 or newer. Only the standard library is needed. The trusted
checker programs never import this file, the producers, or the test fixtures.
"""
import contextlib
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'tests'))
import producer as P
import guarded as G
import protected_producer as N
import measure


CANDIDATES = [
    ('code/checker_bytes.py', 'local', False),
    ('code/checker_ast.py', 'local', False),
    ('code/checker_tokens.py', 'global', False),
    ('code/readable_checker.py', 'local', False),
    ('code/strict_checker.py', 'local', True),
]
BASELINES = [
    ('reference/source_dispatch/code/checker_bytes.py', 'local', False),
    ('reference/source_dispatch/code/checker.py', 'local', False),
    ('reference/source_dispatch/code/checker_tokens.py', 'global', False),
    ('reference/guarded_core/code/checker_bytes.py', 'local', False),
    ('reference/guarded_core/code/checker_ast.py', 'local', False),
    ('reference/guarded_core/code/checker_tokens.py', 'global', False),
]


def check(relative, name, payload, expected, optimized):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT / relative)]
    try:
        process = subprocess.run(command, input=payload, text=True,
                                 capture_output=True, timeout=30)
        accepted = process.returncode == 0 and process.stdout == 'ACCEPT\n'
        error = process.stderr[-1200:]
    except subprocess.TimeoutExpired:
        accepted, error = False, 'Timed out; not an acceptance.'
    row = dict(program=relative, name=name, optimized=optimized,
               expected=expected, accepted=accepted, passed=accepted == expected)
    if not row['passed']:
        row['stderr'] = error
    return row


def as_local(packet):
    packet = json.loads(json.dumps(packet))
    for command in packet[:-1]:
        if isinstance(command, list) and len(command) == 4:
            major, _, initializer, _ = command
            if not major:
                command[0] = []
                if not initializer:
                    command[2] = major
    return packet


def negatives():
    rows = []
    for row in P.build_cases():
        if row['accept'] or row['name'] == 'induction_step_with_base_only_context':
            continue
        if 'proof_tree' in row:
            local = G.LocalEmitter(True).packet(row['proof_tree'])
            local = as_local(local)
        else:
            local = as_local(row['packet'])
        rows.append((row['name'], dict(local=local, global_=row['packet'])))
    for path in sorted((ROOT / 'tests/controls').glob('*.json')):
        packet = json.loads(path.read_text())
        rows.append((path.stem, dict(local=packet, global_=packet)))
    false_goal = P.Emitter().formula(P.Eq(N.W(0), N.W(P.ONE)))
    rows.append(('designated_protected_contradiction', dict(local=[false_goal], global_=[false_goal])))
    return rows


def main():
    output = ROOT / 'evidence'
    output.mkdir(exist_ok=True)
    frozen = json.loads((output / 'frozen_sources.json').read_text())
    for row in frozen:
        path = ROOT / row['local_path']
        data = path.read_bytes()
        git_sha = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if hashlib.sha256(data).hexdigest() != row['sha256'] or git_sha != row['git_blob_sha']:
            raise ValueError('Frozen reference changed: ' + row['local_path'])
    for actual, reference in [('tests/producer.py', 'reference/guarded_core/tests/producer.py'),
                              ('tests/guarded.py', 'reference/guarded_core/tests/build_root_cases.py')]:
        if (ROOT / actual).read_bytes() != (ROOT / reference).read_bytes():
            raise ValueError('Frozen producer copy changed: ' + actual)
    with contextlib.redirect_stdout(io.StringIO()):
        metrics = measure.main()
    examples = N.build(output / 'certificates')
    rows = []
    for program, dialect, _ in CANDIDATES + BASELINES:
        for example in examples:
            source = output / 'certificates' / example['packets'][dialect]['filename']
            payload = source.read_text()
            for optimized in (False, True):
                rows.append(check(program, example['name'], payload, True, optimized))
    negative = negatives()
    malformed = ['', '{', '{}', 'null', 'true', '42', '"x"', '["x"]',
                 '[[true,0,0,0],[0,[0]]]', '[[[0,3.0]]]',
                 '[[[],0,0,0,0],[0,[0]]]']
    for program, dialect, strict in CANDIDATES:
        for name, packets in negative:
            payload = json.dumps(packets['local' if dialect == 'local' else 'global_'])
            for optimized in (False, True):
                rows.append(check(program, name, payload, False, optimized))
        for index, payload in enumerate(malformed):
            for optimized in (False, True):
                rows.append(check(program, 'malformed_' + str(index), payload, False, optimized))
        # A useful explicit boundary: the local profiles initially retain
        # [], an administrative truth alias outside the public language.
        # The inherited global token profile starts with no hypotheses.
        for optimized in (False, True):
            rows.append(check(program, 'administrative_truth_boundary', '[[]]',
                              dialect == 'local' and not strict, optimized))

    # An old valid protected-goal certificate uses literal-zero transport.
    # Guarded-core accepts that old certificate; the combined kernel does not.
    # Its normalized certificate is accepted under the new protocol.
    source_equation = G.sym(P.compute(N.W(0)))
    hole = N.fresh('original_zero_source')
    motive = P.Eq(N.W(P.V(hole)), N.W(P.V(hole)))
    original = P.transport(source_equation, hole, motive, P.reflexivity(N.W(0), N.fresh('r')))
    normalized = N.normalize(P.expand_proof(original))[0]
    for dialect, lexical, neutral in [('local', True, True), ('global', False, False)]:
        old = G.make_packet(original, lexical, neutral)
        new = G.make_packet(normalized, lexical, neutral)
        for variant, packet in [('original', old), ('normalized', new)]:
            (output / 'certificates' / ('zero_source_' + variant + '_' + dialect + '.json')).write_text(
                json.dumps(packet, separators=(',', ':')) + '\n')
        for program, current, _ in CANDIDATES:
            if current != dialect:
                continue
            for optimized in (False, True):
                rows.append(check(program, 'original_zero_source_protocol', json.dumps(old), False, optimized))
                rows.append(check(program, 'normalized_zero_source_protocol', json.dumps(new), True, optimized))
        for program, current, _ in BASELINES[3:]:
            if current == dialect:
                for optimized in (False, True):
                    rows.append(check(program, 'old_guarded_zero_source_protocol', json.dumps(old), True, optimized))

    summary = dict(python=sys.version.split()[0], candidate_programs=len(CANDIDATES),
                   frozen_comparison_programs=len(BASELINES),
                   canonical_named_examples=len(examples), negative_fixture_families=len(negative),
                   total_runs=len(rows), passed=sum(row['passed'] for row in rows),
                   all_passed=all(row['passed'] for row in rows),
                   baseline_envelope=metrics['baseline_envelope'],
                   candidate_envelope=metrics['candidate_envelope'],
                   assurance='Finite execution and syntax audits, not proof-assistant verification.')
    (output / 'validation.json').write_text(json.dumps(dict(summary=summary, results=rows), indent=2) + '\n')
    (output / 'guard_and_source_audits.json').write_text(json.dumps(
        [dict(name=row['name'], audit=row['audit']) for row in examples], indent=2) + '\n')
    print(json.dumps(summary, indent=2))
    if not summary['all_passed']:
        print(json.dumps([row for row in rows if not row['passed']], indent=2))
        raise SystemExit(1)


if __name__ == '__main__':
    main()

"""Regenerate representative derived-zero-source proof certificates.

Examples:
    python3 generate_certificates.py
    python3 generate_certificates.py --local-checker ../code/checker_bytes.py
    python3 generate_certificates.py --global-checker ../code/checker_tokens.py

The producers and normalizer are untrusted. Only the selected standalone
checkers decide acceptance. This script never imports a checker.
"""
import argparse
import json
import subprocess
import sys
from pathlib import Path
import normalizer as n
import global_producer


def examples():
    p = n.p
    yield 'zero_symmetry_one', n.symmetry_fixture()
    yield 'contextual_induction', p.contextual_seed_congruence()
    box = p.I(0, 0, 'zero_box_state', 0)
    major = p.symmetry(p.compute(box), 'given_zero_to_box')
    for binder in ('Q', 'D'):
        prefix, hole = 'zero_under_' + binder, 'zero_under_hole_' + binder
        minor = p.identity_closure(prefix, initial=0)
        body = p.Eq(p.I(p.V(prefix + '_y'), p.V(hole), prefix + '_u', p.V(prefix + '_u')),
                    p.V(hole))
        motive = p.Q(prefix + '_y', body)
        if binder == 'D':
            minor = minor['major']
            motive = p.D(prefix + '_x', prefix + '_y', body)
        yield 'transport_under_' + binder, p.transport(major, hole, motive, minor)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parent / 'fixtures')
    parser.add_argument('--local-checker', type=Path, action='append', default=[])
    parser.add_argument('--global-checker', type=Path, action='append', default=[])
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    report = {'scope': 'Executable examples plus primitive-source audit; not proof-assistant verification.',
              'examples': []}
    failed = False
    for name, original in examples():
        reduced = n.eliminate_zero_sources(original)
        expanded = n.p.expand_proof(reduced)
        row = {'name': name, 'original': n.audit(original),
               'reduced': n.audit(reduced), 'expanded': n.audit(expanded), 'certificates': []}
        assert not row['reduced']['forbidden_zero_sources']
        assert not row['expanded']['forbidden_zero_sources']
        for style, producer, checkers in (('local', n.p, args.local_checker),
                                         ('global', global_producer, args.global_checker)):
            packet = producer.Emitter().packet(reduced)
            path = args.output / (name + '_' + style + '.json')
            text = json.dumps(packet) + '\n'
            path.write_text(text)
            entry = {'file': path.name, 'instructions': len(packet) - 1,
                     'bytes': len(text.encode()), 'checks': []}
            for checker in checkers:
                for mode in ([], ['-O']):
                    run = subprocess.run([sys.executable] + mode + [str(checker.resolve())],
                                         input=text, capture_output=True, text=True)
                    accepted = run.returncode == 0 and run.stdout == 'ACCEPT\n'
                    result = {'checker': checker.name, 'mode': 'optimized' if mode else 'normal',
                              'accepted': accepted}
                    if not accepted:
                        result['stderr_tail'] = run.stderr[-1500:]
                        failed = True
                    entry['checks'].append(result)
            row['certificates'].append(entry)
        report['examples'].append(row)
    report['all_requested_checks_passed'] = not failed
    (args.output / 'validation.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'examples': len(report['examples']),
                      'certificates': sum(len(r['certificates']) for r in report['examples']),
                      'all_requested_checks_passed': not failed,
                      'output': str(args.output.resolve())}, indent=2))
    if failed:
        raise SystemExit(1)


if __name__ == '__main__':
    main()

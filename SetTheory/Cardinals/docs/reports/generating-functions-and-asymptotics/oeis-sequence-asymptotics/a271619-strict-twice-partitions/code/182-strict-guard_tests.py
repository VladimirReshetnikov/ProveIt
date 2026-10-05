#!/usr/bin/env python3
"""Exact-certificate corruption and non-destructive output guards; also under -O."""
from __future__ import annotations
import ast
import contextlib
import copy
import io
import json
import os
from pathlib import Path
import sys
import tempfile
from unittest import mock
sys.dont_write_bytecode = True
ROOT = Path(__file__).absolute().parent
sys.path.insert(0, str(ROOT / 'code'))
import exact
import verify
import regenerate


def need(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    expected = verify.derive()
    verify.same(expected, verify.load_certificate(ROOT / 'data/certificates.json'))
    rejected, accepted = [], []

    def good(label, condition):
        need(condition, label)
        accepted.append(label)

    def bad(label, callback):
        try:
            callback()
        except (ValueError, RuntimeError, TypeError, KeyError, IndexError, OSError, SyntaxError):
            rejected.append(label)
            return
        raise ValueError('expected rejection did not occur: ' + label)

    def leaves(value, path=()):
        if isinstance(value, dict):
            for key, child in sorted(value.items()):
                yield from leaves(child, path + (key,))
        elif isinstance(value, list):
            for index, child in enumerate(value):
                yield from leaves(child, path + (index,))
        else:
            yield path, value

    mutants = []
    for path, value in leaves(expected):
        changed = copy.deepcopy(expected)
        target = changed
        for key in path[:-1]:
            target = target[key]
        target[path[-1]] = (not value if type(value) is bool else value + 1
                            if type(value) is int else str(value) + '#corrupt')
        mutants.append(('scalar leaf ' + repr(path), json.dumps(changed)))
    for label, edit in (
            ('missing field', lambda d: d.pop('scope')),
            ('extra field', lambda d: d.__setitem__('unexpected', 0)),
            ('boolean report', lambda d: d.__setitem__('report', True)),
            ('floating report', lambda d: d.__setitem__('report', 182.0)),
            ('integer for boolean', lambda d: d['scope'].__setitem__('hole_constants_pure_integer_certified', 1)),
            ('float coefficient', lambda d: d['exact_results']['a_first_31'].__setitem__(0, 1.0)),
            ('boolean coefficient', lambda d: d['exact_results']['a_first_31'].__setitem__(0, True)),
            ('noncanonical rational', lambda d: d['exact_results'].__setitem__('crossover_phi', '18/32')),
            ('extra array item', lambda d: d['exact_results']['a_first_31'].append(0))):
        changed = copy.deepcopy(expected)
        edit(changed)
        mutants.append((label, json.dumps(changed)))
    mutants += [('duplicate key', '{"report":182,' + json.dumps(expected)[1:]),
                ('nested duplicate', '{"a":{"b":1,"b":2}}'),
                ('NaN', '{"x":NaN}'), ('Infinity', '{"x":Infinity}'),
                ('trailing JSON', '{} {}'), ('invalid JSON', '{'),
                ('array', '[]'), ('null', 'null')]
    with tempfile.TemporaryDirectory(prefix='report182-corruption-') as temp:
        root = Path(temp)
        damaged = root / 'damaged.json'
        for label, content in mutants:
            damaged.write_text(content)
            bad(label, lambda: verify.same(verify.load_certificate(damaged), expected))
        for label, text in (
                ('missing row', '0 1\n'), ('wrong index', '0 1\n2 1\n'),
                ('decimal', '0 1.0\n1 1\n'), ('negative', '0 -1\n1 1\n'),
                ('double space', '0  1\n1 1\n'), ('leading zero', '0 01\n1 1\n'),
                ('leading zero index', '00 1\n1 1\n'),
                ('no final newline', '0 1\n1 1'), ('extra newline', '0 1\n1 1\n\n'),
                ('CRLF', '0 1\r\n1 1\r\n'), ('extra row', '0 1\n1 1\n2 2\n')):
            damaged.write_bytes(text.encode())
            bad('sequence syntax ' + label, lambda: verify.frozen_terms(damaged, 1))
        damaged.write_text('0 1\n1 1\n')
        good('valid sequence syntax', verify.frozen_terms(damaged, 1) == [1, 1])
        for maximum in (-1, True, 1.0, '1'):
            bad('invalid sequence degree ' + repr(maximum), lambda maximum=maximum:
                verify.frozen_terms(damaged, maximum))
        link = root / 'link.json'
        link.symlink_to(ROOT / 'data/certificates.json')
        parent = root / 'parent'
        parent.symlink_to(root, target_is_directory=True)
        for label, path in [('symlink', link), ('symlink parent', parent / 'damaged.json'),
                            ('missing', root / 'missing'), ('directory', root)]:
            bad(label + ' certificate', lambda path=path: verify.load_certificate(path))
        if hasattr(os, 'mkfifo'):
            os.mkfifo(root / 'pipe')
            bad('FIFO certificate', lambda: verify.load_certificate(root / 'pipe'))
        refs = root / 'references'
        for name in verify.PINS:
            target = refs / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes((ROOT / name).read_bytes())
        with mock.patch.object(verify, 'ROOT', refs):
            good('all frozen reference pins', verify.references() == verify.PINS)
            for name in sorted(verify.PINS):
                target = refs / name
                original = target.read_bytes()
                target.write_bytes(original + b'corrupt')
                bad('frozen reference pin ' + name, verify.references)
                target.write_bytes(original)
        bad('explicit core invariant', lambda: exact.check(False, 'negative control'))
        good('positive core invariant', exact.check(True, 'positive control') is None)
        # Exercise the real CLI parsers and output code, with one already derived
        # result. This isolates output guards from repeated expensive arithmetic.
        def cli(module, arguments):
            out, err = io.StringIO(), io.StringIO()
            with mock.patch.object(sys, 'argv', [str(ROOT / 'fixture.py'), *arguments]), \
                 mock.patch.object(verify, 'derive', return_value=copy.deepcopy(expected)), \
                 contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                status = module.main()
            return status, out.getvalue(), err.getvalue()
        good('CLI accepts exact certificate', cli(verify, [])[0] == 0)
        damaged.write_text(mutants[0][1])
        status, out, err = cli(verify, ['--data', str(damaged)])
        good('CLI rejects corrupted certificate', status == 1 and 'VERIFICATION FAILED:' in err)
        output = root / 'new-certificate.json'
        status, out, err = cli(regenerate, ['--output', str(output), '--compare', str(ROOT / 'data/certificates.json')])
        good('regeneration succeeds', status == 0)
        good('regeneration byte identity', output.read_bytes() == verify.canonical(expected)
             == (ROOT / 'data/certificates.json').read_bytes())
        for label, target in (
                ('existing output', output), ('symlink output', link),
                ('symlink parent', parent / 'forbidden'),
                ('missing parent', root / 'absent' / 'new'),
                ('traversal', root / '..' / 'forbidden'),
                ('inside package', ROOT / 'forbidden-generated.json')):
            status, out, err = cli(regenerate, ['--output', str(target)])
            good('regeneration rejects ' + label, status == 1 and 'REGENERATION FAILED:' in err)
        good('existing certificate preserved', output.read_bytes() == verify.canonical(expected))
        mismatch = root / 'mismatch.json'
        mismatch.write_text('{}')
        target = root / 'mismatched-output'
        status, out, err = cli(regenerate, ['--output', str(target), '--compare', str(mismatch)])
        good('failed comparison writes nothing', status == 1 and not target.exists())
    for script in ('build.py', 'verify_manifest.py', 'test_build.py', 'guard_tests.py',
                   'code/exact.py', 'code/verify.py', 'code/regenerate.py'):
        tree = ast.parse((ROOT / script).read_text())
        good('no removable assertions in ' + script,
             not any(isinstance(node, ast.Assert) for node in ast.walk(tree)))
    tree = ast.parse((ROOT / 'code/exact.py').read_text())
    good('no floating literals in exact core', not any(
        isinstance(node, ast.Constant) and type(node.value) is float for node in ast.walk(tree)))
    print(json.dumps({'status': 'PASS', 'report': 182,
                      'certificate_scalar_leaves_mutated': len(list(leaves(expected))),
                      'corrupt_certificate_variants': len(mutants),
                      'negative_rejections': len(rejected),
                      'positive_checks': len(accepted),
                      'regeneration_byte_identical': True,
                      'runtime_guards_use_assert': False}, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except Exception as exc:
        print('GUARD TEST FAILED: ' + str(exc), file=sys.stderr)
        sys.exit(1)

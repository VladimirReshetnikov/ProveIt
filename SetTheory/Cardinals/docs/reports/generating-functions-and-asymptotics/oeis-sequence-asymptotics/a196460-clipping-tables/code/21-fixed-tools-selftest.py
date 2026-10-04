#!/usr/bin/env python3
"""Owned release-tool tests using synthetic manuscripts and fresh external fixtures.
No scientific executable is imported or run. Use python3 -I -S -B tools/selftest.py
--output-dir /fresh/external/path. This is self-testing, not independent review.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import runpy
import shutil
import struct
import subprocess
import sys
import zlib
import zipfile

ROOT = Path(__file__).absolute().parent.parent


def main():
    if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize):
        raise ValueError('Use python3 -I -S -B without optimization')
    api = runpy.run_path(str(ROOT / 'tools/release.py'), run_name='selftest_release_helpers')
    h = type('Helpers', (), {name: staticmethod(value) if callable(value) else value for name, value in api.items()})
    ap = argparse.ArgumentParser(description=__doc__); ap.add_argument('--output-dir', required=True); a = ap.parse_args()
    out = h.new_output(a.output_dir); out.mkdir(mode=0o700)
    frozen_before = {name: h.snapshot(ROOT / name) for name in ('inputs',)}
    fixture = out / 'fixture'; fixture.mkdir()
    for name in ('inputs',):
        shutil.copytree(ROOT / name, fixture / name, copy_function=shutil.copy2)
    shutil.copy2(ROOT / 'INPUT_PINS.json', fixture / 'INPUT_PINS.json')
    (fixture / 'tools').mkdir()
    for name in ('release.py', 'build_article.py'):
        shutil.copy2(ROOT / 'tools' / name, fixture / 'tools' / name)
    (fixture / 'manuscript').mkdir()
    for name in h.MODULES[1:]:
        (fixture / 'manuscript' / name).write_text('% Synthetic owned smoke module: ' + name + '\n')
    text = ('\\documentclass{article}\n\\IfFileExists{article.aux}{}{\\usepackage{ifthen}}\n'
            '\\pdftrailerid{}\n\\begin{document}\nRelease-only synthetic smoke test.\n' +
            ''.join('\\input{manuscript/' + name + '}\n' for name in h.MODULES[1:]) + '\\end{document}\n')
    (fixture / 'manuscript/article.tex').write_text(text)
    (fixture / 'README.md').write_text('Synthetic release fixture. Not mathematical evidence.\n')
    results = []

    def command(label, tool, args, root=fixture, success=True, env=None):
        result = subprocess.run([sys.executable, '-I', '-S', '-B', str(root / 'tools' / tool), *args], cwd=out,
                                stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300, env=env)
        (out / (label + '.stdout')).write_bytes(result.stdout)
        h.require((result.returncode == 0) == success, 'Unexpected outcome for ' + label + ': ' + result.stdout.decode(errors='replace')[-4000:])
        results.append({'name': label, 'status': 'PASS', 'exit_status': result.returncode})
        return result

    command('input-authentication', 'release.py', ['check-inputs'])
    prepared = out / 'prepared'
    command('deterministic-flatten', 'release.py', ['prepare', '--output-dir', str(prepared)])
    shutil.copy2(prepared / 'article.tex', fixture / 'article.tex')
    shutil.copy2(prepared / 'MANUSCRIPT_PINS.json', fixture / 'manuscript/MANUSCRIPT_PINS.json')
    pin = h.sha((prepared / 'MANUSCRIPT_PINS.json').read_bytes())
    bootstrap = out / 'bootstrap'
    command('fresh-format-bootstrap', 'build_article.py', ['--pins-sha', pin, '--bootstrap', '--output-dir', str(bootstrap)])
    receipt = h.parse((bootstrap / 'BUILD_RECEIPT.json').read_bytes())
    h.require(receipt['status'] == 'BOOTSTRAP' and not receipt['dependency_lock_verified'], 'Bootstrap misrepresented as verified build')
    lockdata = (bootstrap / 'BUILD_DEPENDENCIES.json').read_bytes()
    shutil.copy2(bootstrap / 'BUILD_DEPENDENCIES.json', fixture / 'tools/BUILD_DEPENDENCIES_LOCK.json')
    shutil.copy2(bootstrap / 'article.pdf', fixture / 'article.pdf')
    lockpin = h.sha(lockdata)
    common = ['--pins-sha', pin, '--dependency-lock-sha', lockpin]
    command('locked-rebuild-pdf-equality', 'build_article.py', [*common, '--require-packaged-match', '--output-dir', str(out / 'locked')])
    h.require((out / 'locked/BUILD_DEPENDENCIES.json').read_bytes() == lockdata, 'Dependency receipt not identical to preflight lock')
    union = h.parse((bootstrap / 'RECORDER_INPUT_UNION.json').read_bytes())
    only_first = set(union['passes'][1]['system_inputs']) - set(union['passes'][-1]['system_inputs'])
    early = [p for p in only_first if p.endswith('/ifthen.sty')]
    h.require(len(early) == 1 and early[0] in union['union'], 'First-pass-only input not retained in union')
    results.append({'name': 'first-pass-only-dependency-retained', 'status': 'PASS', 'path': early[0]})

    def clone(label):
        target = out / ('fixture-' + label)
        shutil.copytree(fixture, target, copy_function=shutil.copy2)
        return target

    for variable in ('TMPDIR', 'TEMP', 'TMP'):
        target = clone('hostile-' + variable.lower())
        before = h.snapshot(target)
        hostile_env = os.environ.copy()
        for key in ('TMPDIR', 'TEMP', 'TMP'):
            hostile_env.pop(key, None)
        hostile_env[variable] = str(target / 'inputs/asymptotics')
        command('preserve-input-with-hostile-' + variable.lower(), 'build_article.py',
                [*common, '--require-packaged-match', '--output-dir', str(out / ('hostile-' + variable.lower() + '-build'))],
                root=target, env=hostile_env)
        h.require(h.snapshot(target) == before, 'Inherited ' + variable + ' changed authenticated release')

    wrong = out / 'wrong-pin-output'
    command('reject-manuscript-pin', 'build_article.py', ['--pins-sha', '0' * 64, '--bootstrap', '--output-dir', str(wrong)], success=False)
    h.require(not wrong.exists(), 'Bad manuscript pin created output')
    command('reject-lock-pin', 'build_article.py', ['--pins-sha', pin, '--dependency-lock-sha', '0' * 64, '--output-dir', str(out / 'bad-lock-output')], success=False)
    command('reject-existing-output', 'release.py', ['prepare', '--output-dir', str(prepared)], success=False)
    command('reject-relative-output', 'release.py', ['prepare', '--output-dir', 'relative-output'], success=False)
    command('reject-dotdot-alias', 'release.py', ['prepare', '--output-dir', str(out) + '/../alias-output'], success=False)
    command('reject-release-overlap', 'release.py', ['prepare', '--output-dir', str(fixture / 'unexpected')], success=False)
    command('reject-original-source-overlap', 'release.py', ['prepare', '--output-dir', str(h.PROTECTED[0] / 'unexpected')], success=False)
    (out / 'output-link').symlink_to(out, target_is_directory=True)
    command('reject-output-symlink-ancestor', 'release.py', ['prepare', '--output-dir', str(out / 'output-link/child')], success=False)
    (out / 'fixture-link').symlink_to(fixture, target_is_directory=True)
    command('reject-source-symlink-ancestor', 'release.py', ['check-inputs'], root=out / 'fixture-link', success=False)
    target = clone('extra-input'); (target / 'inputs/asymptotics').chmod(0o755); (target / 'inputs/asymptotics/unexpected.txt').write_text('unexpected')
    command('reject-extra-frozen-file', 'release.py', ['check-inputs'], root=target, success=False)
    target = clone('empty-input'); (target / 'inputs/asymptotics').chmod(0o755); (target / 'inputs/asymptotics/empty').mkdir()
    command('reject-extra-empty-directory', 'release.py', ['check-inputs'], root=target, success=False)
    target = clone('hardlink'); os.link(target / 'README.md', target / 'hardlink.md')
    command('reject-hardlinked-input', 'release.py', ['check-inputs'], root=target, success=False)
    target = clone('symlink'); (target / 'extra-symlink').symlink_to(target / 'README.md')
    command('reject-symlinked-input', 'release.py', ['check-inputs'], root=target, success=False)
    target = clone('source-mode'); p = target / 'inputs/asymptotics/PROOF.md'; p.chmod(p.stat().st_mode ^ 0o100)
    command('reject-source-mode-change', 'release.py', ['check-inputs'], root=target, success=False)
    target = clone('source-mtime'); p = target / 'inputs/asymptotics/PROOF.md'; os.utime(p, ns=(p.stat().st_mtime_ns + 1, p.stat().st_mtime_ns + 1))
    command('reject-source-mtime-change', 'release.py', ['check-inputs'], root=target, success=False)
    target = clone('early-dependency'); changed = h.parse(lockdata); del changed['system_inputs'][early[0]]
    data = h.encoded(changed); (target / 'tools/BUILD_DEPENDENCIES_LOCK.json').write_bytes(data)
    command('reject-omitted-first-pass-dependency', 'build_article.py', ['--pins-sha', pin, '--dependency-lock-sha', h.sha(data), '--output-dir', str(out / 'omitted-first-pass')], root=target, success=False)
    target = clone('stale-system'); changed = h.parse(lockdata); changed['system_inputs'][early[0]]['sha256'] = '0' * 64
    data = h.encoded(changed); (target / 'tools/BUILD_DEPENDENCIES_LOCK.json').write_bytes(data)
    dest = out / 'stale-system-output'
    command('reject-stale-system-preflight', 'build_article.py', ['--pins-sha', pin, '--dependency-lock-sha', h.sha(data), '--output-dir', str(dest)], root=target, success=False)
    h.require(not dest.exists(), 'Stale system pin passed preflight')

    builder = runpy.run_path(str(ROOT / 'tools/build_article.py'), run_name='selftest_png_validation')
    def chunk(kind, payload):
        return struct.pack('>I', len(payload)) + kind + payload + struct.pack('>I', zlib.crc32(kind + payload) & 0xffffffff)
    png = b'\x89PNG\r\n\x1a\n' + chunk(b'IHDR', struct.pack('>IIBBBBB', 1, 1, 8, 2, 0, 0, 0)) + chunk(b'IDAT', zlib.compress(b'\x00\x00\x00\x00')) + chunk(b'IEND', b'')
    h.require(builder['validate_png'](png, h.require) == {'width': 1, 'height': 1}, 'Valid synthetic PNG rejected')
    for label, data in [('truncated', png[:-1]), ('crc', png[:45] + bytes([png[45] ^ 1]) + png[46:]), ('trailing', png + b'bad'), ('empty', b'')]:
        try:
            builder['validate_png'](data, h.require)
        except (ValueError, zlib.error):
            results.append({'name': 'reject-png-' + label, 'status': 'PASS'})
        else:
            raise ValueError('Corrupt PNG accepted: ' + label)

    collision = {'format': h.FORMAT,
                 'files': {h.MANIFEST + '/child.txt': {'mode': 0o644, 'mtime_ns': 1, 'bytes': 0, 'sha256': h.sha(b'')}},
                 'directories': {h.MANIFEST: {'mode': 0o755, 'mtime_ns': 1}}}
    try:
        h.validate_manifest(collision)
    except ValueError:
        results.append({'name': 'reject-manifest-directory-collision', 'status': 'PASS'})
    else:
        raise ValueError('Manifest-directory collision accepted')

    manifest_file = out / 'manifest.json'
    command('manifest-generation', 'release.py', ['manifest', '--output', str(manifest_file)])
    shutil.copy2(manifest_file, fixture / h.MANIFEST)
    manifest_pin = h.sha(manifest_file.read_bytes())
    command('manifest-verification', 'release.py', ['verify', '--manifest-sha256', manifest_pin])
    for suffix in ('a', 'b'):
        command('deterministic-archive-' + suffix, 'release.py', ['archive', '--manifest-sha256', manifest_pin, '--output', str(out / ('archive-' + suffix + '.zip'))])
    h.require((out / 'archive-a.zip').read_bytes() == (out / 'archive-b.zip').read_bytes(), 'Repeated ZIP bytes differ')
    extracted = out / 'extracted'
    command('metadata-preserving-extraction', 'release.py', ['extract', '--manifest-sha256', manifest_pin, '--archive', str(out / 'archive-a.zip'), '--output-dir', str(extracted)])
    command('relocated-manifest-verification', 'release.py', ['verify', '--manifest-sha256', manifest_pin], root=extracted)
    command('relocated-pdf-rebuild-equality', 'build_article.py', [*common, '--require-packaged-match', '--output-dir', str(out / 'relocated-build')], root=extracted)
    target = clone('manifest-tamper'); (target / 'README.md').write_text('tampered')
    command('reject-manifest-content-tamper', 'release.py', ['verify', '--manifest-sha256', manifest_pin], root=target, success=False)
    malicious = out / 'archive-extra.zip'
    shutil.copy2(out / 'archive-a.zip', malicious)
    with zipfile.ZipFile(malicious, 'a') as archive:
        archive.writestr('../escape.txt', b'not allowed')
    rejected = out / 'rejected-extract'
    command('reject-archive-path-traversal', 'release.py', ['extract', '--manifest-sha256', manifest_pin, '--archive', str(malicious), '--output-dir', str(rejected)], success=False)
    h.require(not rejected.exists(), 'Unsafe archive created extraction output')
    frozen_after = {name: h.snapshot(ROOT / name) for name in ('inputs',)}
    h.require(frozen_before == frozen_after, 'Real frozen inputs changed during selftests')
    receipt = {'status': 'PASS', 'scope': 'Owned release-tool selftests on synthetic TeX; not independent review or scientific evidence', 'tests': results,
               'test_count': len(results), 'first_pass_only_input': early[0], 'dependency_lock_sha256': lockpin, 'frozen_inputs_preserved': True,
               'tool_sources': {name: h.sha((ROOT / 'tools' / name).read_bytes()) for name in ('release.py', 'build_article.py', 'selftest.py')}}
    (out / 'SELFTEST_RECEIPT.json').write_bytes(h.encoded(receipt))
    print(h.encoded(receipt).decode())


if __name__ == '__main__':
    main()

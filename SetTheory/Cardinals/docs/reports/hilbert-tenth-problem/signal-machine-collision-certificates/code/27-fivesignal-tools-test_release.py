#!/usr/bin/env python3
"""Adversarial synthetic-fixture tests; never mutate or seal the real release.

Run: python3 -I tools/test_release.py --output /absolute/new/test-directory
Add --with-pdf to build a tiny, original synthetic TeX document twice.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import stat
import subprocess
import sys
import zipfile


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def write_new(path, data):
    with path.open('xb') as stream:
        stream.write(data)
    path.chmod(0o644)


def snapshot(root):
    result = {}
    for path in [root] + sorted(root.rglob('*')):
        info = path.lstat()
        row = [info.st_mode, info.st_mtime_ns, info.st_ino, info.st_nlink]
        if stat.S_ISREG(info.st_mode):
            row.append(sha(path.read_bytes()))
        elif stat.S_ISLNK(info.st_mode):
            row.append(os.readlink(path))
        result[str(path.relative_to(root))] = row
    return result


def main():
    need(sys.flags.isolated == 1 and sys.flags.optimize == 0, 'Run python3 -I, without -O')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    parser.add_argument('--with-pdf', action='store_true')
    args = parser.parse_args()
    raw = args.output
    output = Path(raw)
    need(not raw.startswith('//') and str(output) == raw, 'Canonical path required')
    need(output.is_absolute() and not any(p in ('.', '..') for p in raw.split('/')), 'Absolute fresh path required')
    for path in reversed([output] + list(output.parents)[:-1]):
        if path == output:
            need(not os.path.lexists(path), 'Test output exists')
        else:
            info = path.lstat()
            need(stat.S_ISDIR(info.st_mode), 'Output ancestor must be a nonsymlink directory')
    own_root = Path(__file__).absolute().parent.parent
    need(output != own_root and own_root not in output.parents and output not in own_root.parents,
         'Tests must be outside the real release')
    output.mkdir(mode=0o755)
    original = snapshot(own_root / 'tools')
    fixture = output / 'fixture'
    fixture.mkdir(mode=0o755)
    (fixture / 'tools').mkdir(mode=0o755)
    (fixture / 'assets').mkdir(mode=0o755)
    script = fixture / 'tools/release.py'
    write_new(script, (own_root / 'tools/release.py').read_bytes())
    tex = (r'\documentclass{article}' '\n' r'\usepackage[T1]{fontenc}' '\n'
           r'\usepackage{lmodern}' '\n' r'\begin{document}' '\n'
           r'Report57 synthetic release-tool test.\input{assets/guards.tex}' '\n'
           r'\input{assets/rules.tex}\end{document}' '\n').encode()
    write_new(fixture / 'Report57.tex', tex)
    write_new(fixture / 'assets/guards.tex', b'An inert guard table.\n')
    write_new(fixture / 'assets/rules.tex', b'An inert rule table.\n')
    checks = []
    def invoke(argv, success=True, python_flags=('-I',), env=None, target=script):
        proc = subprocess.run([sys.executable, *python_flags, str(target), *map(str, argv)],
                              stdin=subprocess.DEVNULL, capture_output=True, text=True,
                              timeout=360, env=env)
        need((proc.returncode == 0) == success,
             'Unexpected status for %r: %s %s' % (argv, proc.stdout[-2000:], proc.stderr[-3000:]))
        return json.loads(proc.stdout) if success else proc.stderr
    def guard(label, argv, python_flags=('-I',), target=script):
        before = snapshot(fixture)
        invoke(argv, success=False, python_flags=python_flags, target=target)
        need(snapshot(fixture) == before, 'Rejected operation changed fixture: ' + label)
        checks.append(label)
    pdf = None
    dependencies = None
    if args.with_pdf:
        poison = output / 'poison'
        poison.mkdir()
        write_new(poison / 'article.cls', b'\\errmessage{Inherited TEXINPUTS contamination}\n')
        env = dict(os.environ, TEXINPUTS=str(poison), TEXMFHOME=str(poison), SOURCE_DATE_EPOCH='1')
        first = invoke(['build-pdf', '--draft', '--output', output / 'build-a'], env=env)
        lock = output / 'build-a/dependency-manifest.json'
        dependencies = lock.read_bytes()
        second = invoke(['build-pdf', '--draft', '--output', output / 'build-b',
                         '--dependency-lock', lock, '--dependency-lock-sha256', sha(dependencies)])
        pdf = (output / 'build-a/Report57.pdf').read_bytes()
        need(pdf == (output / 'build-b/Report57.pdf').read_bytes(), 'Synthetic PDF is not reproducible')
        need(dependencies == (output / 'build-b/dependency-manifest.json').read_bytes(), 'TeX dependency lock varies')
        need(first['inherited_environment'] is False and second['dependency_lock_verified'], 'Missing environment/dependency receipt')
        checks += ['synthetic_pdf_identical_clean_builds', 'inherited_TEXINPUTS_and_epoch_ignored',
                   'external_dependency_lock_verified', 'dependency_inventory_reproducible']
    write_new(fixture / 'Report57.pdf', pdf or b'%PDF-synthetic-fixture-only\n')
    sealed = invoke(['seal'])
    pin = sealed['manifest_sha256']
    invoke(['verify', '--manifest-sha256', pin])
    checks.append('exact_seal_and_verify')
    guard('reject_reseal', ['seal'])
    guard('reject_wrong_manifest_pin', ['verify', '--manifest-sha256', '0' * 64])
    guard('reject_nonisolated_python', ['verify', '--manifest-sha256', pin], python_flags=())
    guard('reject_optimized_python', ['verify', '--manifest-sha256', pin], python_flags=('-I', '-O'))
    manifest = fixture / 'MANIFEST.json'
    manifest_bytes = manifest.read_bytes()
    manifest.unlink()
    manifest.symlink_to(output / 'absent-manifest-target')
    guard('reject_dangling_manifest_reseal', ['seal'])
    guard('reject_dangling_manifest_verify', ['verify', '--manifest-sha256', pin])
    manifest.unlink()
    write_new(manifest, b'{"schema": "x", "schema": "x"}\n')
    guard('reject_duplicate_manifest_json_keys', ['verify', '--manifest-sha256', sha(manifest.read_bytes())])
    manifest.write_bytes(b'{"schema": NaN}\n')
    guard('reject_nonfinite_manifest_json', ['verify', '--manifest-sha256', sha(manifest.read_bytes())])
    manifest.write_bytes(manifest_bytes)
    archive_base = ['archive', '--manifest-sha256', pin, '--output']
    existing = output / 'existing.zip'
    write_new(existing, b'KEEP THIS OUTPUT\n')
    directory = output / 'existing-dir.zip'
    directory.mkdir()
    write_new(directory / 'keep', b'keep\n')
    live = output / 'live.zip'
    live.symlink_to(existing)
    dangling = output / 'dangling.zip'
    dangling.symlink_to(output / 'missing-target')
    fifo = output / 'special.zip'
    os.mkfifo(fifo)
    parent_link = output / 'parent-link'
    parent_link.symlink_to(directory, target_is_directory=True)
    for label, target in [('existing_file', existing), ('existing_directory', directory),
                          ('live_symlink', live), ('dangling_symlink', dangling), ('fifo_output', fifo),
                          ('symlink_parent', parent_link / 'fresh.zip'), ('inside_release', fixture / 'nested.zip'),
                          ('missing_parent', output / 'missing-parent/archive.zip'),
                          ('double_slash_alias', '/' + str(fixture / 'alias.zip')),
                          ('repeated_separator_alias', str(output) + '//fixture/alias.zip'),
                          ('parent_traversal', str(output) + '/fixture/../new.zip')]:
        outside_before = snapshot(output)
        guard('reject_' + label, archive_base + [target])
        need(snapshot(output) == outside_before, 'Rejected output changed existing path: ' + label)
    for label, target in [('build_existing_dir', directory), ('build_existing_file', existing),
                          ('build_dangling', dangling), ('build_inside_release', fixture / 'fresh-build'),
                          ('build_source_root', fixture), ('build_parent', output)]:
        outside_before = snapshot(output)
        guard('reject_' + label, ['build-pdf', '--draft', '--output', target])
        need(snapshot(output) == outside_before, 'Rejected build changed existing output: ' + label)
    original_tex = (fixture / 'Report57.tex').read_bytes()
    (fixture / 'Report57.tex').write_bytes(original_tex + b'% tampered\n')
    guard('detect_content_tamper', ['verify', '--manifest-sha256', pin])
    (fixture / 'Report57.tex').write_bytes(original_tex)
    (fixture / 'Report57.tex').chmod(0o600)
    guard('detect_mode_tamper', ['verify', '--manifest-sha256', pin])
    (fixture / 'Report57.tex').chmod(0o644)
    missing = fixture / 'assets/rules.tex'
    missing_bytes = missing.read_bytes()
    missing.unlink()
    guard('detect_file_removal', ['verify', '--manifest-sha256', pin])
    write_new(missing, missing_bytes)
    extra = fixture / 'empty-extra-dir'
    extra.mkdir()
    guard('detect_empty_directory_addition', ['verify', '--manifest-sha256', pin])
    extra.rmdir()
    extra = fixture / 'extra-file'
    write_new(extra, b'x')
    guard('detect_file_addition', ['verify', '--manifest-sha256', pin])
    extra.unlink()
    extra.symlink_to(output / 'no-such-target')
    guard('detect_dangling_input_symlink', ['verify', '--manifest-sha256', pin])
    extra.unlink()
    extra.symlink_to(directory, target_is_directory=True)
    guard('detect_input_directory_symlink', ['verify', '--manifest-sha256', pin])
    extra.unlink()
    os.mkfifo(extra)
    guard('detect_input_fifo', ['verify', '--manifest-sha256', pin])
    extra.unlink()
    os.link(fixture / 'Report57.tex', extra)
    guard('detect_hardlinked_input', ['verify', '--manifest-sha256', pin])
    extra.unlink()
    alias = output / 'root-alias'
    alias.symlink_to(fixture, target_is_directory=True)
    guard('detect_release_root_alias', ['verify', '--manifest-sha256', pin], target=alias / 'tools/release.py')
    guard('reject_dependency_wrong_pin_before_output', ['build-pdf', '--draft', '--output', output / 'wrong-lock-build',
          '--dependency-lock', fixture / 'MANIFEST.json', '--dependency-lock-sha256', '0' * 64])
    need(not os.path.lexists(output / 'wrong-lock-build'), 'Bad dependency pin created output')
    if args.with_pdf:
        sealed_build = invoke(['build-pdf', '--output', output / 'sealed-build', '--manifest-sha256', pin,
                              '--dependency-lock', output / 'build-a/dependency-manifest.json',
                              '--dependency-lock-sha256', sha(dependencies)])
        need(sealed_build['packaged_pdf_identical'], 'Sealed PDF did not reproduce')
        checks.append('sealed_pdf_rebuild_identical')
    first_zip = invoke(archive_base + [output / 'one.zip'])
    second_zip = invoke(archive_base + [output / 'two.zip'])
    need((output / 'one.zip').read_bytes() == (output / 'two.zip').read_bytes(), 'ZIP output not deterministic')
    checks.append('stored_zip_byte_identical')
    race_before = snapshot(fixture)
    argv = [sys.executable, '-I', str(script), *map(str, archive_base + [output / 'race.zip'])]
    processes = [subprocess.Popen(argv, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                                  stderr=subprocess.PIPE, text=True) for _ in range(2)]
    for proc in processes:
        proc.communicate(timeout=60)
    need(sorted(proc.returncode == 0 for proc in processes) == [False, True], 'Exclusive archive race did not have one winner')
    need((output / 'race.zip').read_bytes() == (output / 'one.zip').read_bytes(), 'Archive race damaged the winner')
    need(snapshot(fixture) == race_before, 'Archive race changed source')
    checks.append('concurrent_archive_exclusive_single_winner')
    moved = output / 'relocated'
    moved.mkdir()
    with zipfile.ZipFile(output / 'one.zip') as bundle:
        bundle.extractall(moved)
        for member in bundle.infolist():
            (moved / member.filename).chmod((member.external_attr >> 16) & 0o777)
    moved.chmod(0o755)
    invoke(['verify', '--manifest-sha256', pin], target=moved / 'tools/release.py')
    moved_zip = invoke(archive_base + [output / 'relocated.zip'], target=moved / 'tools/release.py')
    need(first_zip['zip_sha256'] == moved_zip['zip_sha256'], 'Relocated archive differs')
    checks += ['relocated_archive_exact_verification', 'relocated_archive_byte_identical']
    need(snapshot(own_root / 'tools') == original, 'Tests changed real release tools')
    result = {'schema': 'report57-release-tools-tests-v1', 'status': 'PASS', 'checks_passed': len(checks),
              'checks': checks, 'release_tool_sha256': sha(script.read_bytes()),
              'synthetic_pdf_tested': args.with_pdf, 'real_manuscript_built_or_sealed': False,
              'real_release_tools_preserved': True, 'synthetic_zip_sha256': first_zip['zip_sha256'],
              'synthetic_pdf_sha256': sha(pdf) if pdf else None,
              'synthetic_tex_dependency_manifest_sha256': sha(dependencies) if dependencies else None}
    payload = (json.dumps(result, sort_keys=True, indent=2) + '\n').encode()
    write_new(output / 'tools-test-receipt.json', payload)
    sys.stdout.buffer.write(payload)


if __name__ == '__main__':
    main()

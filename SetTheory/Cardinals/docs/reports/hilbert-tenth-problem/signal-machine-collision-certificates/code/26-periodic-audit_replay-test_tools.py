#!/usr/bin/env python3
"""New Report56 utility adversarial tests; operate only in a fresh external tree.

Exercises copied release.py on a synthetic TeX fixture, and the pinned replay
on original read-only inputs plus deliberately damaged temporary copies. Never
seals the real release. Run python3 -I without -O. Requires installed pdflatex.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys

ROOT = Path(__file__).absolute().parents[1]

def require(value, message):
    if not value:
        raise RuntimeError(message)

def walk_error(error):
    raise error

def sha(data):
    return hashlib.sha256(data).hexdigest()

def snapshot(root):
    entries = {}
    for base, dirs, files in os.walk(root, followlinks=False, onerror=walk_error):
        base = Path(base)
        for path in [base] + [base / name for name in sorted(dirs + files)]:
            rel = '.' if path == root else path.relative_to(root).as_posix()
            info = path.lstat()
            row = [info.st_mode, info.st_mtime_ns]
            if stat.S_ISREG(info.st_mode):
                row += [sha(path.read_bytes())]
            elif stat.S_ISLNK(info.st_mode):
                row += [os.readlink(path)]
            entries[rel] = row
    return entries

def main():
    require(sys.flags.isolated and not sys.flags.optimize, 'Use python3 -I without -O')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    out = args.output
    require(out.is_absolute() and '..' not in out.parts, 'Absolute output without traversal required')
    for path in [out] + list(out.parents):
        require(not path.is_symlink(), 'No output path symlinks')
    require(not os.path.lexists(out) and out.parent.is_dir(), 'Fresh output with existing parent required')
    require(out != ROOT and ROOT not in out.parents and out not in ROOT.parents, 'External output required')
    for rel in ('science', 'independent_audit', 'audit_replay/immutable-inputs.json'):
        require((ROOT / rel).exists(), 'Final frozen inputs must be packaged first')
    inputs_before = {name: snapshot(ROOT / name) for name in ('science', 'independent_audit')}
    out.mkdir(mode=0o700)
    results = []
    python = str(Path(sys.executable).resolve())
    def invoke(label, argv, passed=True, preserve=(), absent=()):
        before = {str(path): snapshot(path) for path in preserve}
        proc = subprocess.run([python, '-I', '-B', *argv], cwd=out, stdin=subprocess.DEVNULL,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=1500, check=False)
        (out / (label + '.stdout')).write_bytes(proc.stdout)
        (out / (label + '.stderr')).write_bytes(proc.stderr)
        require((proc.returncode == 0) == passed, label + ' unexpected return code: ' + proc.stderr.decode())
        for path in preserve:
            require(snapshot(path) == before[str(path)], label + ' changed protected tree')
        for path in absent:
            require(not os.path.lexists(path), label + ' created a rejected output')
        results.append({'test': label, 'status': 'PASS', 'expected_success': passed})
        return json.loads(proc.stdout) if passed else None
    fixture = out / 'release-fixture'
    fixture.mkdir(mode=0o755)
    (fixture / 'article').mkdir(mode=0o755)
    shutil.copy2(ROOT / 'release.py', fixture / 'release.py')
    (fixture / 'article/Report56.tex').write_text('\\pdfinfoomitdate=1\n\\pdftrailerid{}\n\\documentclass{article}\n'
        '\\begin{document}\nNewly authored release-tool fixture. Arithmetic replay is not a simulator.\n\\end{document}\n')
    release = str(fixture / 'release.py')
    invoke('release-draft-build', [release, 'build-pdf', '--draft', '--output', str(out / 'pdf-draft')], preserve=(fixture,))
    shutil.copy2(out / 'pdf-draft/Report56.pdf', fixture / 'article/Report56.pdf')
    seal = invoke('release-seal-fixture', [release, 'seal'])
    pin = seal['manifest_sha256']
    verify = [release, 'verify', '--manifest-sha256', pin]
    invoke('release-verify', verify, preserve=(fixture,))
    invoke('release-seal-no-overwrite', [release, 'seal'], False, preserve=(fixture,))
    for suffix in ('one', 'two'):
        invoke('release-sealed-build-' + suffix, [release, 'build-pdf', '--manifest-sha256', pin,
               '--output', str(out / ('pdf-' + suffix))], preserve=(fixture,))
        invoke('release-stored-archive-' + suffix, [release, 'archive', '--manifest-sha256', pin,
               '--output', str(out / ('archive-' + suffix + '.zip'))], preserve=(fixture,))
    require((out / 'pdf-one/Report56.pdf').read_bytes() == (out / 'pdf-two/Report56.pdf').read_bytes(), 'PDF determinism')
    require((out / 'archive-one.zip').read_bytes() == (out / 'archive-two.zip').read_bytes(), 'ZIP determinism')
    results.append({'test': 'independent-output-pdf-and-zip-byte-determinism', 'status': 'PASS', 'expected_success': True})
    alias = out / 'symlink-parent'; alias.symlink_to(out / 'pdf-one', target_is_directory=True)
    dangling = out / 'dangling-output'; dangling.symlink_to(out / 'absent-destination')
    for label, target in [('reused', out / 'pdf-one'), ('nested', fixture / 'nested-output'),
                          ('symlink-parent', alias / 'child'), ('symlink-leaf', dangling)]:
        absent = () if os.path.lexists(target) else (target,)
        invoke('release-reject-' + label, [release, 'build-pdf', '--draft', '--output', str(target)],
               False, preserve=(fixture,), absent=absent)
    invoke('release-reject-optimized', ['-O', release, 'verify', '--manifest-sha256', pin], False, preserve=(fixture,))
    for damage in ('tampered', 'missing', 'extra-file', 'extra-directory', 'mode', 'symlink'):
        clone = out / ('damaged-release-' + damage)
        shutil.copytree(fixture, clone, copy_function=shutil.copy2)
        target = clone / 'article/Report56.tex'
        if damage == 'tampered': target.write_bytes(target.read_bytes() + b'% altered\n')
        elif damage == 'missing': target.unlink()
        elif damage == 'extra-file': (clone / 'extra.txt').write_text('extra')
        elif damage == 'extra-directory': (clone / 'empty-extra').mkdir()
        elif damage == 'mode': target.chmod(0o600)
        elif damage == 'symlink': target.unlink(); target.symlink_to(fixture / 'article/Report56.tex')
        invoke('release-reject-' + damage, [str(clone / 'release.py'), 'verify', '--manifest-sha256', pin],
               False, preserve=(clone, fixture))
    unreadable = out / 'release-unreadable-fixture'
    shutil.copytree(fixture, unreadable, copy_function=shutil.copy2)
    hidden = unreadable / 'extra-unreadable-directory'; hidden.mkdir(); hidden.chmod(0)
    try:
        invoke('release-reject-unreadable-extra-directory', [str(unreadable / 'release.py'), 'verify',
               '--manifest-sha256', pin], False, preserve=(fixture,))
    finally:
        hidden.chmod(0o700)
    replay = str(ROOT / 'audit_replay/replay_audit.py')
    replay_output = out / 'arithmetic-replay'
    replay_receipt = invoke('replay-positive', [replay, '--output', str(replay_output)],
                           preserve=(ROOT / 'science', ROOT / 'independent_audit'))
    for label, target in [('reused', replay_output), ('nested-release', ROOT / 'rejected-replay-output'),
                          ('nested-science', ROOT / 'science/rejected-replay-output'),
                          ('nested-audit', ROOT / 'independent_audit/rejected-replay-output'),
                          ('symlink-parent', alias / 'replay'), ('symlink-leaf', dangling)]:
        absent = () if os.path.lexists(target) else (target,)
        invoke('replay-reject-' + label, [replay, '--output', str(target)], False,
               preserve=(ROOT / 'science', ROOT / 'independent_audit'), absent=absent)
    opt = out / 'optimized-output'
    invoke('replay-reject-optimized', ['-O', replay, '--output', str(opt)], False,
           preserve=(ROOT / 'science', ROOT / 'independent_audit'), absent=(opt,))
    for source_name, option, target_name in [('science', '--packet', 'PROOF.md'),
                                            ('independent_audit', '--audit', 'check-results.json')]:
        for damage in ('tampered', 'missing', 'extra-file', 'extra-directory', 'mode', 'symlink'):
            label = source_name + '-' + damage
            clone = out / ('damaged-input-' + label)
            shutil.copytree(ROOT / source_name, clone, copy_function=shutil.copy2)
            target = clone / target_name
            if damage == 'tampered': target.write_bytes(target.read_bytes() + b'altered\n')
            elif damage == 'missing': target.unlink()
            elif damage == 'extra-file': (clone / 'extra.txt').write_text('extra')
            elif damage == 'extra-directory': (clone / 'extra-directory').mkdir()
            elif damage == 'mode': target.chmod(0o600)
            elif damage == 'symlink': target.unlink(); target.symlink_to(ROOT / source_name / target_name)
            target_out = out / ('rejected-' + label)
            invoke('replay-reject-' + label, [replay, option, str(clone), '--output', str(target_out)], False,
                   preserve=(clone, ROOT / 'science', ROOT / 'independent_audit'), absent=(target_out,))
    for source_name, option in [('science', '--packet'), ('independent_audit', '--audit')]:
        clone = out / ('unreadable-input-' + source_name)
        shutil.copytree(ROOT / source_name, clone, copy_function=shutil.copy2)
        hidden = clone / 'extra-unreadable-directory'; hidden.mkdir(); hidden.chmod(0)
        target_out = out / ('rejected-unreadable-' + source_name)
        try:
            invoke('replay-reject-unreadable-' + source_name, [replay, option, str(clone), '--output', str(target_out)],
                   False, preserve=(ROOT / 'science', ROOT / 'independent_audit'), absent=(target_out,))
        finally:
            hidden.chmod(0o700)
    # An inventory alteration is rejected by the code pin even if file content is valid JSON.
    clone_release = out / 'inventory-pin-fixture'; (clone_release / 'audit_replay').mkdir(parents=True)
    shutil.copy2(ROOT / 'audit_replay/replay_audit.py', clone_release / 'audit_replay/replay_audit.py')
    data = (ROOT / 'audit_replay/immutable-inputs.json').read_bytes()
    (clone_release / 'audit_replay/immutable-inputs.json').write_bytes(data + b'\n')
    target_out = out / 'rejected-inventory-pin'
    invoke('replay-reject-inventory-pin', [str(clone_release / 'audit_replay/replay_audit.py'),
           '--packet', str(ROOT / 'science'), '--audit', str(ROOT / 'independent_audit'), '--output', str(target_out)],
           False, preserve=(clone_release, ROOT / 'science', ROOT / 'independent_audit'), absent=(target_out,))
    require({name: snapshot(ROOT / name) for name in inputs_before} == inputs_before, 'Original inputs changed')
    result = {'schema': 'report56-tools-adversarial-validation-v1', 'status': 'PASS', 'tests': results,
              'test_count': len(results), 'original_science_and_audit_bytes_modes_mtimes_preserved': True,
              'real_release_sealed': False, 'synthetic_fixture_only_for_release_seal_and_pdf_tests': True,
              'utility_sha256': {name: sha((ROOT / name).read_bytes()) for name in
                 ('release.py', 'audit_replay/replay_audit.py', 'audit_replay/immutable-inputs.json', 'audit_replay/test_tools.py')},
              'replay_receipt_sha256': sha((replay_output / 'replay-receipt.json').read_bytes())}
    payload = (json.dumps(result, sort_keys=True, indent=2) + '\n').encode()
    (out / 'tools-validation.json').write_bytes(payload)
    sys.stdout.buffer.write(payload)

if __name__ == '__main__':
    main()

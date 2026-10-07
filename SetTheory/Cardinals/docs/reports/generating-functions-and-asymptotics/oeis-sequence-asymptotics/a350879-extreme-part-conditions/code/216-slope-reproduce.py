#!/usr/bin/env python3
"""Rebuild Report216 exact receipts, diagnostics, PDF, and deterministic ZIP offline."""
import argparse
import ast
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys
import zipfile
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
PDF = 'Report216.pdf'
MANIFEST = 'MANIFEST.json'
FORMAT = 'Report216 SHA256 manifest v1'


def require(ok, message):
    if not ok:
        raise RuntimeError('CHECK_FAILED[package]: ' + message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read_json(path):
    def unique(pairs):
        obj = {}
        for key, value in pairs:
            require(key not in obj, 'duplicate JSON key ' + key)
            obj[key] = value
        return obj
    return json.loads(path.read_text(encoding='utf-8'), object_pairs_hook=unique)


def write_json(path, obj):
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + '\n', encoding='utf-8')


def safe_name(name):
    require(type(name) is str and bool(name), 'empty/non-string inventory path')
    p = PurePosixPath(name)
    require(p.as_posix() == name and name != '.' and chr(92) not in name
            and not p.is_absolute() and '..' not in p.parts, 'unsafe inventory path ' + name)
    return name


def source_names(root=ROOT):
    names = (root/'SOURCE_FILES.txt').read_text(encoding='utf-8').splitlines()
    require(len(names) == len(set(names)), 'duplicate source inventory entry')
    require('SOURCE_FILES.txt' in names and 'reproduce.py' in names, 'incomplete source inventory')
    require(PDF not in names and MANIFEST not in names, 'reserved generated file in source inventory')
    for name in names:
        safe_name(name)
        p = root/name
        require(p.is_file() and not p.is_symlink(), 'missing/linked source ' + name)
        if name.endswith('.py'):
            tree = ast.parse(p.read_text(encoding='utf-8'))
            require(not any(isinstance(n, ast.Assert) for n in ast.walk(tree)), 'assert statement in ' + name)
    expected = set(names) | {PDF, MANIFEST}
    actual = set()
    for p in root.rglob('*'):
        require(not p.is_symlink(), 'linked package path ' + str(p.relative_to(root)))
        if p.is_file() and '__pycache__' not in p.parts:
            actual.add(p.relative_to(root).as_posix())
    require(actual <= expected, 'unlisted package files ' + repr(sorted(actual-expected)))
    return sorted(names)


def verify_manifest(root, names):
    obj = read_json(root/MANIFEST)
    require(type(obj) is dict and set(obj) == {'format', 'files'}, 'manifest shape')
    require(obj['format'] == FORMAT, 'manifest format')
    require(type(obj['files']) is dict and set(obj['files']) == set(names), 'manifest inventory mismatch')
    for name in names:
        safe_name(name)
        require(obj['files'][name] == sha((root/name).read_bytes()), 'manifest byte mismatch ' + name)


def validate_output(candidate, root=ROOT):
    require(not candidate.exists() and not candidate.is_symlink(), 'output already exists or is a symbolic link')
    out = candidate.resolve()
    root = root.resolve()
    require(out != root and root not in out.parents and out not in root.parents, 'output overlaps source tree')
    require(not out.exists(), 'output already exists')
    require(out.parent.is_dir(), 'output parent does not exist')
    return out


def run(command, cwd, log, env=None):
    result = subprocess.run(command, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log.write_text(result.stdout, encoding='utf-8')
    require(result.returncode == 0, 'command failed; inspect ' + str(log))
    return result.stdout


def make_pdf(stage, logs):
    env = os.environ.copy()
    env.update(SOURCE_DATE_EPOCH='1791072000', FORCE_SOURCE_DATE='1', TZ='UTC', LC_ALL='C')
    dist = Path(run(['kpsewhich', '-var-value=TEXMFDIST'], stage, logs/'texdist.log', env).strip())
    require(dist.is_dir(), 'installed TeX tree missing')
    trees = [dist]
    sibling = dist.parent.parent/'texmf'
    if sibling.is_dir():
        trees.append(sibling)
    env['TEXMF'] = '{'+','.join(map(str, trees))+'}'
    env['TEXFORMATS'] = str(stage)+os.pathsep
    # A private format avoids writes to a user's TeX cache in a clean environment.
    run(['pdftex', '-ini', '-etex', '-no-shell-escape', '-interaction=nonstopmode',
         '-halt-on-error', '-jobname=pdflatex', 'pdflatex.ini'], stage, logs/'format.log', env)
    require((stage/'pdflatex.fmt').is_file(), 'private TeX format missing')
    maps = []
    for name in ['cm.map', 'cmextra.map', 'latxfont.map', 'symbols.map', 'euler.map', 'lm.map']:
        path = Path(run(['kpsewhich', name], stage, logs/(name+'.log'), env).strip())
        require(path.is_file(), 'font map missing ' + name)
        maps.append(path.read_bytes())
    (stage/'pdftex.map').write_bytes(b'\n'.join(maps)+b'\n')
    previous, stable = None, False
    for i in range(1, 7):
        run(['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
             '-halt-on-error', 'Report216.tex'], stage, logs/f'latex{i}.log', env)
        current = (stage/PDF).read_bytes()
        if i >= 3 and current == previous:
            stable = True
            break
        previous = current
    require(stable, 'PDF did not reach byte stability')
    latex = (logs/f'latex{i}.log').read_text(encoding='utf-8')
    for phrase in ['Overfull \\hbox', 'Overfull \\vbox', 'undefined references', 'undefined citations']:
        require(phrase not in latex, 'TeX diagnostic ' + phrase)


def archive(root, names, path):
    require(names == sorted(set(names)), 'ZIP inventory must be unique and sorted')
    with zipfile.ZipFile(path, 'w', compression=zipfile.ZIP_STORED) as z:
        for name in names:
            safe_name(name)
            info = zipfile.ZipInfo('Report216/'+name, (2026, 10, 4, 0, 0, 0))
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            z.writestr(info, (root/name).read_bytes())
    verify_zip(root, names, path)


def verify_zip(root, names, path):
    with zipfile.ZipFile(path) as z:
        require(z.namelist() == ['Report216/'+name for name in names], 'actual ZIP inventory mismatch')
        require(z.testzip() is None, 'ZIP CRC failure')
        for name in names:
            require(z.read('Report216/'+name) == (root/name).read_bytes(), 'actual ZIP member mismatch ' + name)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True, help='New directory outside the source tree')
    parser.add_argument('--reference-zip', type=Path, help='Verify and compare to this actual original ZIP')
    parser.add_argument('--initialize', action='store_true', help='Authoring only: permit absent PDF/manifest baseline')
    parser.add_argument('--self-test-failure', action='store_true', help='Intentionally fail before output writes')
    args = parser.parse_args()
    require(not args.self_test_failure, 'intentional pre-write failure')
    out = validate_output(args.out)
    names = source_names()
    members = sorted(names+[PDF])
    if not args.initialize:
        verify_manifest(ROOT, members)
    if args.reference_zip:
        require(args.reference_zip.is_file(), 'reference ZIP missing')
        require(not args.initialize, 'reference comparison requires a complete baseline')
        verify_zip(ROOT, sorted(members+[MANIFEST]), args.reference_zip)
    out.mkdir()
    stage, logs, fresh = out/'Report216', out/'logs', out/'fresh'
    stage.mkdir(); logs.mkdir()
    for name in names:
        (stage/name).parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT/name, stage/name)
    flags = ['-O'] if sys.flags.optimize else []
    # All exact outputs are independently regenerated in both Python modes.
    for suffix, mode in [('normal', []), ('optimized', ['-O'])]:
        target = fresh/suffix
        run([sys.executable, '-B', *mode, 'code/reproduce.py', '--exact', '--out', str(target)],
            stage, logs/('exact-'+suffix+'.log'))
        require({p.relative_to(target).as_posix() for p in target.rglob('*') if p.is_file()} ==
                {'results/exact_checks.json', 'results/coefficients.json', 'results/selected_counts.json'},
                'fresh exact inventory mismatch')
        for p in sorted(target.rglob('*')):
            if p.is_file():
                relative = p.relative_to(target)
                baseline = stage/'code'/relative if relative.parts[0] == 'results' else stage/relative
                require(p.read_bytes() == baseline.read_bytes(), 'fresh exact mismatch ' + relative.as_posix())
    # Diagnostics rebuild all large counts instead of trusting a saved numerical file.
    diagnostic = fresh/'diagnostics'
    run([sys.executable, '-B', *flags, 'code/reproduce.py', '--diagnostics', '--out', str(diagnostic)],
        stage, logs/'diagnostics.log')
    require({p.relative_to(diagnostic).as_posix() for p in diagnostic.rglob('*') if p.is_file()} ==
            {'results/diagnostics.json', 'tables/forward_table.tex', 'tables/inverse_table.tex'},
            'fresh diagnostic inventory mismatch')
    for p in sorted(diagnostic.rglob('*')):
        if p.is_file():
            relative = p.relative_to(diagnostic)
            baseline = stage/'code'/relative if relative.parts[0] == 'results' else stage/relative
            require(p.read_bytes() == baseline.read_bytes(), 'fresh diagnostic mismatch ' + relative.as_posix())
    pair = []
    for suffix, mode in [('normal', []), ('optimized', ['-O'])]:
        raw = run([sys.executable, '-B', *mode, 'test_package_guards.py'], stage,
                  logs/('guards-'+suffix+'.log'))
        pair.append(json.dumps(json.loads(raw), indent=2, sort_keys=True)+'\n')
    require(pair[0] == pair[1], 'package guard mode mismatch')
    require(pair[0] == (stage/'PACKAGE_GUARD_CHECKS.json').read_text(), 'package guard baseline mismatch')
    make_pdf(stage, logs)
    if (ROOT/PDF).exists():
        require((stage/PDF).read_bytes() == (ROOT/PDF).read_bytes(), 'PDF baseline mismatch; check TeX/font toolchain')
    else:
        require(args.initialize, 'PDF baseline absent')
    for name in ['Report216.aux', 'Report216.log', 'Report216.out', 'Report216.toc',
                 'pdflatex.fmt', 'pdflatex.log', 'pdftex.map', 'texsys.aux']:
        if (stage/name).exists():
            (stage/name).unlink()
    require({p.relative_to(stage).as_posix() for p in stage.rglob('*') if p.is_file()} == set(members),
            'staged package has missing or unexpected files')
    write_json(stage/MANIFEST, {'format': FORMAT, 'files': {name: sha((stage/name).read_bytes()) for name in members}})
    if not args.initialize:
        require((stage/MANIFEST).read_bytes() == (ROOT/MANIFEST).read_bytes(), 'manifest rebuild mismatch')
    verify_manifest(stage, members)
    allmembers = sorted(members+[MANIFEST])
    result_zip = out/'Report216-reproducibility.zip'
    archive(stage, allmembers, result_zip)
    if args.reference_zip:
        require(result_zip.read_bytes() == args.reference_zip.read_bytes(), 'actual reference ZIP byte mismatch')
    result = {'status': 'PASS', 'exact_regeneration_both_modes': True,
              'diagnostics_regenerated': True, 'package_guards_both_modes': True,
              'pdf_byte_stability': True, 'reference_zip_checked': bool(args.reference_zip),
              'pdf_sha256': sha((stage/PDF).read_bytes()), 'zip_sha256': sha(result_zip.read_bytes()),
              'manifest_sha256': sha((stage/MANIFEST).read_bytes()), 'archive_members': len(allmembers)}
    write_json(out/'REPRODUCTION.json', result)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()

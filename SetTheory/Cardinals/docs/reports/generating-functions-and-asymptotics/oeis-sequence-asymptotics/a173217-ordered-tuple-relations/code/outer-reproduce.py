#!/usr/bin/env python3
"""Rebuild Report220 exact data, PDF and deterministic ZIP without network access."""
import argparse
import ast
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import zipfile
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
PDF = 'Report220.pdf'
MANIFEST = 'MANIFEST.json'


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


def run(cmd, cwd, log, env=None):
    result = subprocess.run(cmd, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log.write_text(result.stdout, encoding='utf-8')
    require(result.returncode == 0, 'command failed; inspect ' + str(log))
    return result.stdout


def source_names():
    names = (ROOT/'SOURCE_FILES.txt').read_text(encoding='utf-8').splitlines()
    require(len(names) == len(set(names)), 'duplicate source inventory entry')
    require('SOURCE_FILES.txt' in names and 'reproduce.py' in names, 'incomplete source inventory')
    for name in names:
        p = Path(name)
        require(name and not p.is_absolute() and '..' not in p.parts, 'unsafe source path')
        require((ROOT/p).is_file() and not (ROOT/p).is_symlink(), 'missing or linked source '+name)
        if name.endswith('.py'):
            tree = ast.parse((ROOT/p).read_text(encoding='utf-8'))
            require(not any(isinstance(n, ast.Assert) for n in ast.walk(tree)), 'assert in '+name)
    return sorted(names)


def verify_manifest(root, names):
    obj = read_json(root/MANIFEST)
    require(obj.get('format') == 'Report220 SHA256 manifest v1', 'manifest format')
    require(set(obj.get('files', {})) == set(names), 'manifest inventory mismatch')
    for name in names:
        require(obj['files'][name] == sha((root/name).read_bytes()), 'manifest byte mismatch '+name)


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
    run(['pdftex', '-ini', '-etex', '-no-shell-escape', '-interaction=nonstopmode',
         '-halt-on-error', '-jobname=pdflatex', 'pdflatex.ini'], stage, logs/'format.log', env)
    require((stage/'pdflatex.fmt').is_file(), 'private format missing')
    maps = []
    for name in ['cm.map', 'cmextra.map', 'latxfont.map', 'symbols.map', 'euler.map', 'lm.map']:
        path = Path(run(['kpsewhich', name], stage, logs/(name+'.log'), env).strip())
        require(path.is_file(), 'font map missing '+name)
        maps.append(path.read_bytes())
    (stage/'pdftex.map').write_bytes(b'\n'.join(maps)+b'\n')
    previous, stable = None, False
    for i in range(1, 7):
        run(['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
             '-halt-on-error', 'Report220.tex'], stage, logs/f'latex{i}.log', env)
        current = (stage/PDF).read_bytes()
        if i >= 3 and current == previous:
            stable = True
            break
        previous = current
    require(stable, 'PDF did not reach byte stability')
    latex = (logs/f'latex{i}.log').read_text(encoding='utf-8')
    for phrase in ['Overfull \\hbox', 'Overfull \\vbox', 'undefined references', 'undefined citations']:
        require(phrase not in latex, 'TeX diagnostic '+phrase)


def archive(root, names, path):
    with zipfile.ZipFile(path, 'w', compression=zipfile.ZIP_STORED) as z:
        for name in names:
            info = zipfile.ZipInfo('Report220/'+name, (2026, 10, 4, 0, 0, 0))
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            z.writestr(info, (root/name).read_bytes())
    with zipfile.ZipFile(path) as z:
        require(z.namelist() == ['Report220/'+name for name in names], 'actual ZIP inventory mismatch')
        require(z.testzip() is None, 'ZIP CRC failure')
        for name in names:
            require(z.read('Report220/'+name) == (root/name).read_bytes(), 'actual ZIP member mismatch '+name)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True, help='New directory outside the source tree')
    parser.add_argument('--reference-zip', type=Path, help='Compare rebuilt bytes to this actual original ZIP')
    parser.add_argument('--initialize', action='store_true', help='Authoring only: allow absent PDF/manifest baseline')
    parser.add_argument('--self-test-failure', action='store_true', help='Intentionally fail before output writes')
    args = parser.parse_args()
    require(not args.self_test_failure, 'intentional pre-write failure')
    digit_limit = sys.get_int_max_str_digits() if hasattr(sys, 'get_int_max_str_digits') else 0
    require(digit_limit == 0 or digit_limit >= 4300,
            'full reproduction includes mpmath diagnostics and requires the default integer digit limit 4300 or higher; standalone code/rational_checks.py recovery supports 640 without changing that input limit')
    require(not args.out.exists() and not args.out.is_symlink(), 'output already exists or is a symbolic link')
    out = args.out.resolve()
    require(out != ROOT and ROOT not in out.parents and out not in ROOT.parents, 'output overlaps source tree')
    require(not out.exists(), 'output already exists')
    require(out.parent.is_dir(), 'output parent does not exist')
    names = source_names()
    members = sorted(names+[PDF])
    if not args.initialize:
        verify_manifest(ROOT, members)
    if args.reference_zip:
        require(args.reference_zip.is_file(), 'reference ZIP missing')
    out.mkdir()
    stage, logs = out/'Report220', out/'logs'
    stage.mkdir()
    logs.mkdir()
    for name in names:
        (stage/name).parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT/name, stage/name)
    flags = ['-O'] if sys.flags.optimize else []
    run([sys.executable, '-B', *flags, 'code/reproduce.py', '--output-dir', str(out/'finite')],
        stage, logs/'finite.log')
    evidence = read_json(out/'finite'/'reproduction_receipt.json')
    # Read freshly regenerated bytes, compare baseline, and carry those actual bytes forward.
    for name in ['hierarchy_coefficients.json', 'check_results.json', 'rational_checks.json',
                 'negative_controls.json', 'recovery_example.json', 'reproduction_receipt.json']:
        actual = (out/'finite'/name).read_bytes()
        require(actual == (ROOT/'code'/'results'/name).read_bytes(), 'fresh finite result mismatch '+name)
        (stage/'code'/'results'/name).write_bytes(actual)
    make_pdf(stage, logs)
    if (ROOT/PDF).exists():
        require((stage/PDF).read_bytes() == (ROOT/PDF).read_bytes(), 'PDF baseline mismatch; check TeX/font toolchain')
    else:
        require(args.initialize, 'PDF baseline absent')
    obj = {'format': 'Report220 SHA256 manifest v1',
           'files': {name: sha((stage/name).read_bytes()) for name in members}}
    write_json(stage/MANIFEST, obj)
    if not args.initialize:
        require((stage/MANIFEST).read_bytes() == (ROOT/MANIFEST).read_bytes(), 'manifest rebuild mismatch')
    verify_manifest(stage, members)
    allmembers = sorted(members+[MANIFEST])
    result_zip = out/'Report220-reproducibility.zip'
    archive(stage, allmembers, result_zip)
    reference_checked = False
    if args.reference_zip:
        require(result_zip.read_bytes() == args.reference_zip.read_bytes(), 'actual whole-ZIP byte mismatch')
        reference_checked = True
    receipt = {'all_checks_passed': True, 'source_baselines_verified': not args.initialize,
               'python_optimization': sys.flags.optimize, 'fresh_finite_replay': evidence,
               'pdf_rebuilt_to_byte_stability': True, 'actual_zip_members_verified': True,
               'actual_reference_whole_zip_verified': reference_checked,
               'archive_sha256': sha(result_zip.read_bytes()), 'zip_member_count': len(allmembers),
               'member_sha256': {name: sha((stage/name).read_bytes()) for name in allmembers}}
    write_json(out/'reproduction.json', receipt)
    print(json.dumps(receipt, indent=2, sort_keys=True))

if __name__ == '__main__':
    main()

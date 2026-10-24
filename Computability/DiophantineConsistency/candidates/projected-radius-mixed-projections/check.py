#!/usr/bin/env python3
"""Check every integer restoration and quartic coefficient without an optimizer."""
import argparse
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import zipfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REPO = ROOT.parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
from review_synchronized_certificates import full_sos


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(data):
    return sha256(data).hexdigest()


def load(name):
    return json.loads((HERE / name).read_text())


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    pins = load('SOURCE_PINS.json')
    parent_dir = ROOT / pins['parent_directory']
    for name, expected in pins['parent_files'].items():
        need(digest((parent_dir / name).read_bytes()) == expected, 'frozen mixed994 parent ' + name)
    manifest = json.loads((parent_dir / 'MANIFEST.json').read_text())['files']
    need({str(p.relative_to(parent_dir)) for p in parent_dir.rglob('*')
          if p.is_file() and p.name != 'MANIFEST.json'} == set(manifest), 'closed parent file set')
    for name, expected in manifest.items():
        need(digest((parent_dir / name).read_bytes()) == expected, 'whole sealed mixed-domain foundation ' + name)
    for name, expected in pins['independent_repository_helpers'].items():
        need(digest((ROOT / name).read_bytes()) == expected, 'independent repository helper ' + name)
    build = load('BUILD.json')
    need(digest((HERE / 'build.py').read_bytes()) == build['generator_sha256'], 'producer pin')
    for name, expected in build['sha256'].items():
        need(digest((HERE / name).read_bytes()) == expected, 'whole generated child artifact ' + name)
    parent = json.loads((parent_dir / 'equation.json').read_text())
    archive = REPO / pins['arithmetic_archive']
    need(digest(archive.read_bytes()) == pins['arithmetic_archive_sha256'], 'whole inherited arithmetic archive')
    results = {}
    mutations = []
    with zipfile.ZipFile(archive) as z, tempfile.TemporaryDirectory(prefix='mixed994-independent-projections-') as tmp:
        code = Path(tmp)
        for name, expected in pins['read_source_members'].items():
            need(digest(z.read(name)) == expected, 'exact source member ' + name)
            if Path(name).name != 'terminal_elimination.py':
                (code / Path(name).name).write_bytes(z.read(name))
        # The producer/optimizer file is deliberately never imported here.
        sys.path.insert(0, str(code))
        from verify_projection import verify
        older_checks = module('frozen_integer_restoration_controls',
                              ROOT / 'candidates/projected-radius-integers/check.py')
        for name in ['support4', 'support8', 'support16', 'support32']:
            child = load(name + '/equation.json')
            certificate = load(name + '/elimination_certificate.json')
            need(certificate['unconstrained_removed'] == [], 'entire mixed integer parent uniquely restored')
            review = verify(parent, child, certificate)
            metrics = full_sos(child, load(name + '/expanded_polynomial.json'))
            signed_controls = older_checks.restoration_controls(parent, child, certificate)
            results[name] = dict(restoration=review, metrics=metrics,
                                 arbitrary_signed_restoration_controls=signed_controls)
            bad = deepcopy(certificate)
            bad['steps'][0]['restoration'][0][0] += 1
            try:
                verify(parent, child, bad)
            except ValueError:
                mutations.append('changed restoration ' + name)
            else:
                raise ValueError('changed restoring polynomial accepted')
            bad = load(name + '/expanded_polynomial.json')
            bad['terms'][0][0] += 1
            try:
                full_sos(child, bad)
            except RuntimeError:
                mutations.append('changed collected coefficient ' + name)
            else:
                raise ValueError('changed collected coefficient accepted')
        bad = deepcopy(load('support32/equation.json'))
        bad['residuals'].pop()
        try:
            verify(parent, bad, load('support32/elimination_certificate.json'), check_hashes=False)
        except ValueError:
            mutations.append('omitted current residual with hashes bypassed')
        else:
            raise ValueError('omitted actual residual accepted')
    # Recheck the frozen domain theorem's finite premises after the pure Z maps.
    command = [sys.executable, '-B'] + (['-O'] if sys.flags.optimize else []) + [str(parent_dir / 'check.py')]
    proc = subprocess.run(command, capture_output=True, text=True)
    need(proc.returncode == 0, 'complete frozen mixed-domain checker: ' + proc.stderr)
    foundation = json.loads(proc.stdout)
    need(foundation['status'] == 'PASS' and foundation['metrics']['variables'] == 994,
         'actual mixed994 finite foundation')
    result = dict(status='PASS', optimized_python=bool(sys.flags.optimize), variants=results,
        rejected_corruptions=mutations,
        foundation=dict(command=command, status='PASS', stdout_sha256=digest(proc.stdout.encode()),
                        complete_arithmetic_boundary=foundation['complete_arithmetic_boundary'],
                        mixed_sign_certificate=foundation['sign_certificate']),
        scope='Every reverse integer map is checked first, including all guard equations. The frozen mixed sign ledger and positive-comparison normalization then establish natural-source existence. No pointwise natural restoration or Lean/internal-ZFC claim.')
    text = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Fresh signed monic projections of the frozen mixed994 parent."""
import argparse
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import tempfile
import zipfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REPO = ROOT.parents[1]
PARENT = ROOT / 'candidates/projected-radius-mixed'
ARCHIVE = REPO / 'docs/incoming/ConZFC_407_888_Quartics_2026-10-24.zip'
ARCHIVE_SHA = '59f847872298260ee35e9d8e4cd0b52d2d78658ac523981fe060e81f40ca4a59'
MEMBER = 'ConZFC_407_888_Quartics/code/integer_pipeline/terminal_elimination.py'
CAPS = [4, 8, 16, 32]


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode()


def generate():
    pins = json.loads((HERE / 'SOURCE_PINS.json').read_text())
    for name, expected in pins['parent_files'].items():
        need(digest((PARENT / name).read_bytes()) == expected, 'frozen mixed994 parent ' + name)
    parent = json.loads((PARENT / 'equation.json').read_text())
    need(len(parent['variables']) == 994 and len(parent['residuals']) == 694
         and parent['domain'] == 'unrestricted integers', 'actual complete integer parent')
    need(digest(ARCHIVE.read_bytes()) == ARCHIVE_SHA == pins['arithmetic_archive_sha256'], 'whole arithmetic archive')
    files = {}
    census = {}
    with zipfile.ZipFile(ARCHIVE) as z, tempfile.TemporaryDirectory(prefix='mixed994-project-') as tmp:
        path = Path(tmp) / 'terminal_elimination.py'
        raw = z.read(MEMBER)
        need(digest(raw) == pins['producer_member_sha256'], 'exact generic integer optimizer bytes')
        path.write_bytes(raw)
        spec = importlib.util.spec_from_file_location('mixed994_signed_optimizer', path)
        engine = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(engine)
        for cap in CAPS:
            child, cert, metrics = engine.optimize(parent, max_support=cap)
            need(cert['unconstrained_removed'] == [], 'every parent coordinate uniquely restored')
            review = engine.verify(parent, child, cert)
            polynomial = engine.expand(child)
            name = 'support' + str(cap)
            payload = {'equation.json': child, 'elimination_certificate.json': cert,
                       'expanded_polynomial.json': polynomial,
                       'BUILD.json': dict(metrics=metrics, producer_internal_verification=review,
                                          support_cap=cap)}
            for filename, value in payload.items():
                files[name + '/' + filename] = encoded(value)
            census[name] = dict(metrics=child['metrics'], support_cap=cap,
                                eliminated_coordinates=len(cert['steps']), unconstrained_removed=[])
    files['CENSUS.json'] = encoded(census)
    files['BUILD.json'] = encoded(dict(status='PASS', generator_sha256=digest(Path(__file__).read_bytes()),
        sha256={name: digest(raw) for name, raw in files.items()},
        scope='Complete new projected quartics, all original guards included in every substitution. Independent verifier and mixed-domain ordinary proof are separate.'))
    return files, census


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    files, census = generate()
    for name, raw in files.items():
        path = HERE / name
        if args.check:
            need(path.read_bytes() == raw, 'deterministic projected artifact ' + name)
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
    print(json.dumps(dict(status='PASS', check=args.check,
        metrics={name: {k: item['metrics'][k] for k in ['variables', 'quadratic_rows',
            'expanded_monomials', 'max_abs_expanded_coefficient']} for name, item in census.items()}), indent=2))


if __name__ == '__main__':
    main()

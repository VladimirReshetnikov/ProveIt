#!/usr/bin/env python3
"""Exact signed monic projections of the frozen synchronized integer systems.

Reads the original signed optimizer from its authenticated arrival archive.
No arithmetic compiler, proof assistant, network or satisfiability solver is run.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys
import zipfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
DEST = ROOT / 'candidates/synchronized-signed-projections'
PARENT = ROOT / 'candidates/synchronized-row-guards'
ARCHIVE = REPO / 'docs/incoming/con_zfc_batched_certificates_2026-10-23.zip'
ARCHIVE_SHA = 'ff0d3f638d91a905f676f6fe3e40e134979a14880ed34cadf0741604386e8e55'
SOURCE_PINS = {
    'terminal_elimination.py': '73ca399b859116cedd9b2b7cb107c82926421697f41ee63b9b61f8bc6c1c0027',
    'verify_projection.py': '6c097d79f0ab37e97db3df452afc43f20897fee42e4935af56206fc8f1c1fb3b',
    'audit_common_radix.py': '5852e74a1c6bb3aa8614d6f0d2d229a89f3ca70e226f59116980ab9297f4376c',
}
PARENT_EQ = {
    'integer1224': 'f34bc294d33f4d2bab8b9e745ee27df98c5385f8a95d220cfa9bde39a710d167',
    'integer1231': '2a7248de119600cd7a7d9fb51ba90f4de05d03ed431f70654ea28f7071be1219',
    'integer1298': '5fd1448595a29d2457867be4389e23cd69bc8e7a611fbc177a8ca397f686dcea',
}
PARENT_POLY = {
    'integer1224': '56a04bcebdf9edf75922699d35018fc2a60b19310db5a9e53a9efd7a59989200',
    'integer1231': '1c786d2e4c05c53cf077da58b15077faf97e5960413f351ed8cda4f5aeeec79c',
    'integer1298': '0b07d848705be460590b5909f2670d5716c26f2fd6558c9c92d75c7d2363764e',
}
SELECTED = {
    ('integer1224', 4, False): 'from1224-support4',
    ('integer1231', 4, False): 'from1231-support4',
    ('integer1231', 8, False): 'from1231-support8',
    ('integer1298', 4, False): 'from1298-support4',
    ('integer1298', 8, False): 'from1298-support8',
    ('integer1298', 8, True): 'from1298-support8-quadratic',
    ('integer1298', 16, True): 'from1298-support16-quadratic',
}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return sha256(raw).hexdigest()


def encoded(obj):
    return (json.dumps(obj, sort_keys=True, separators=(',', ':')) + '\n').encode()


def build():
    need(digest(ARCHIVE.read_bytes()) == ARCHIVE_SHA, 'whole signed-optimizer archive pin')
    files = {}
    with zipfile.ZipFile(ARCHIVE) as archive:
        for name, expected in SOURCE_PINS.items():
            raw = archive.read('con-zfc-batched-certificates/integer/' + name)
            need(digest(raw) == expected, 'authentic signed module ' + name)
            files['source/' + name] = raw
        license_member = 'con-zfc-batched-certificates/LICENSE'
        files['source/LICENSE'] = archive.read(license_member)
    ns = {'__name__': '_authenticated_signed_optimizer', '__file__': str(DEST / 'source/terminal_elimination.py')}
    exec(compile(files['source/terminal_elimination.py'], ns['__file__'], 'exec'), ns)
    optimize, verify, expand = (ns[x] for x in ('optimize', 'verify', 'expand'))
    parent_hashes = {}
    probes = []
    selections = {}
    for parent_name in PARENT_EQ:
        for name in ('equation.json', 'expanded_polynomial.json', 'natural_parent.json',
                     'NONNEGATIVITY.json', 'PARENT_PINS.json'):
            raw = (PARENT / parent_name / name).read_bytes()
            files['parents/' + parent_name + '/' + name] = raw
        raw = files['parents/' + parent_name + '/equation.json']
        need(digest(raw) == PARENT_EQ[parent_name], 'frozen integer parent')
        need(digest(files['parents/' + parent_name + '/expanded_polynomial.json']) == PARENT_POLY[parent_name], 'frozen full quartic')
        equation = json.loads(raw)
        parent_hashes[parent_name] = {n: digest(files['parents/' + parent_name + '/' + n])
            for n in ('equation.json', 'expanded_polynomial.json', 'natural_parent.json', 'NONNEGATIVITY.json', 'PARENT_PINS.json')}
        for support in (4, 8, 16):
            for quadratic_first in (False, True):
                child, certificate, measurements = optimize(equation, max_support=support, quadratic_first=quadratic_first)
                need(not certificate['unconstrained_removed'], 'require bijection: no unconstrained-coordinate deletion')
                # Parent seed/index metadata refers to the unprojected coordinate system.
                # It belongs to the copied parent packet, never to the child equation.
                child = {k: child[k] for k in ('schema', 'domain', 'polynomial', 'variables', 'residuals')}
                child['metrics'] = {k: measurements[k] for k in
                    ('expanded_monomials', 'exact_degree', 'max_abs_expanded_coefficient', 'max_abs_row_coefficient')}
                child['metrics'].update(variables=len(child['variables']), quadratic_rows=len(child['residuals']))
                child['elimination'] = {'method': 'integral monic quadratic substitution',
                                        'certificate': 'terminal_elimination_certificate.json'}
                certificate['output_sha256'] = digest(encoded(child))
                verify(equation, child, certificate)
                signed = sum(any(c < 0 for c, _ in step['restoration']) for step in certificate['steps'])
                record = dict(parent=parent_name, max_support=support, quadratic_first=quadratic_first,
                              metrics=measurements, signed_restoration_steps=signed,
                              equation_sha256=digest(encoded(child)), certificate_sha256=digest(encoded(certificate)))
                probes.append(record)
                key = (parent_name, support, quadratic_first)
                if key in SELECTED:
                    target = SELECTED[key]
                    selections[target] = record
                    for name, value in [('equation.json', child), ('terminal_elimination_certificate.json', certificate),
                                        ('expanded_polynomial.json', expand(child))]:
                        files[target + '/' + name] = encoded(value)
    pins = dict(schema='synchronized_signed_projection_pins_v1', optimizer_archive=str(ARCHIVE.relative_to(REPO)),
        optimizer_archive_sha256=ARCHIVE_SHA, optimizer_members=SOURCE_PINS,
        parent_root=str(PARENT.relative_to(ROOT)), parent_files=parent_hashes,
        generator_sha256=digest(Path(__file__).read_bytes()), selected=selections)
    files['PROVENANCE.json'] = encoded(pins)
    files['PROBES.json'] = encoded(dict(status='PASS', configurations=probes,
        scope='All 18 fixed support/order configurations, not a global optimality claim. All coordinates are unrestricted integers.'))
    hashes = {name: digest(raw) for name, raw in sorted(files.items())}
    files['BUILD.json'] = encoded(dict(status='PASS', sha256=hashes, selected=selections,
        scope='Exact signed monic substitutions; independent replay and restored row-sign certificates are checked separately. No Lean or internal-ZFC derivation.'))
    return files, selections


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    files, selections = build()
    for name, raw in files.items():
        target = DEST / name
        if args.check:
            need(target.read_bytes() == raw, 'byte-identical regeneration ' + name)
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(raw)
    print(json.dumps(dict(status='PASS', check=args.check, selected={name: item['metrics'] for name, item in selections.items()}), indent=2))


if __name__ == '__main__':
    main()

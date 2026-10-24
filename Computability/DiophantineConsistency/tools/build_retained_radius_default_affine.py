#!/usr/bin/env python3
"""Exact frozen raw1493 input, default-affine support8 integer projection only."""
import argparse
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import zipfile
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
HERE = ROOT/'candidates/retained-radius-default-affine'
PARENT = ROOT/'candidates/retained-radius-comparison-base'
PARENT_MANIFEST = 'f956fa4306ce698920ca847426c8beebe6e5a0ed14c229923111e4bca74d40f0'
PARENT_EQUATION = 'c30bee5671a654988f4ffa1eb5e5b43469b000292f4e78a85f5c062c0239494e'
ARCHIVE = 'docs/incoming/ConZFC_407_888_Quartics_2026-10-24.zip'
ARCHIVE_SHA = '59f847872298260ee35e9d8e4cd0b52d2d78658ac523981fe060e81f40ca4a59'
MEMBER = 'ConZFC_407_888_Quartics/code/integer_pipeline/terminal_elimination.py'
MEMBER_SHA = '73ca399b859116cedd9b2b7cb107c82926421697f41ee63b9b61f8bc6c1c0027'
COPY = {'guarded.json':'guarded.json','domain_certificate.json':'domain_certificate.json',
        'BRIDGE901.json':'BRIDGE901.json','LIFT904.json':'LIFT904.json',
        'PROOF.md':'PARENT_PROOF.md','MANIFEST.json':'PARENT_MANIFEST.json',
        'SOURCE_PINS.json':'PARENT_SOURCE_PINS.json'}

def need(ok, message):
    if not ok:
        raise ValueError(message)

def digest(data):
    return sha256(data).hexdigest()

def encoded(value):
    return (json.dumps(value,sort_keys=True,separators=(',',':'))+'\n').encode()

def generate():
    need(digest((PARENT/'MANIFEST.json').read_bytes()) == PARENT_MANIFEST, 'complete frozen parent inventory')
    parent_manifest = json.loads((PARENT/'MANIFEST.json').read_bytes())['files']
    need({str(p.relative_to(PARENT)) for p in PARENT.rglob('*') if p.is_file() and p.name!='MANIFEST.json'}
         == set(parent_manifest), 'closed immutable parent')
    for name, expected in parent_manifest.items():
        need(digest((PARENT/name).read_bytes()) == expected, 'whole parent member '+name)
    parent_bytes = (PARENT/'guarded.json').read_bytes()
    need(digest(parent_bytes) == PARENT_EQUATION, 'EXACT source coefficients, metadata and labels')
    parent = json.loads(parent_bytes)
    need(len(parent['variables']) == 1493 and len(parent['residuals']) == 1255,
         'complete raw source and78 private triples')
    files = {'source/'+dest:(PARENT/source).read_bytes() for source,dest in COPY.items()}
    inherited = json.loads((PARENT/'SOURCE_PINS.json').read_bytes())
    pins = dict(inherited['files'])
    for name in list(parent_manifest)+['MANIFEST.json']:
        p = PARENT/name
        pins[str(p.relative_to(ROOT))] = digest(p.read_bytes())
    for name in ['candidates/retained-radius-bounds/check.py',
                 'candidates/projected-radius-mixed/check.py',
                 'tools/review_synchronized_certificates.py','tools/review_quartics407888.py']:
        pins[name] = digest((ROOT/name).read_bytes())
    for name,h in pins.items():
        need(digest((ROOT/name).read_bytes()) == h, 'whole source dependency '+name)
    files['SOURCE_PINS.json'] = encoded(dict(schema='retained_default_affine_full_source_pins_v1',
        parent='candidates/retained-radius-comparison-base',parent_equation_sha256=PARENT_EQUATION,
        parent_manifest_sha256=PARENT_MANIFEST,files=pins,
        raw_foundation=inherited['raw_foundation'],foundation901=inherited['foundation901'],
        archive=ARCHIVE,archive_sha256=ARCHIVE_SHA,optimizer_member=MEMBER,optimizer_member_sha256=MEMBER_SHA,
        source_metadata_or_labels_changed=False,guard_exchange_applied=False))
    archive = REPO/ARCHIVE
    need(digest(archive.read_bytes()) == ARCHIVE_SHA, 'whole arithmetic archive')
    with zipfile.ZipFile(archive) as z:
        data = z.read(MEMBER)
    need(digest(data) == MEMBER_SHA, 'exact reviewed terminal optimizer')
    with tempfile.TemporaryDirectory(prefix='raw1493-default-affine-') as tmp:
        module_path = Path(tmp)/'terminal_elimination.py'
        module_path.write_bytes(data)
        spec = importlib.util.spec_from_file_location('raw1493_default_affine_optimizer',module_path)
        engine = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(engine)
        child, certificate, metrics = engine.optimize(parent,max_support=8)
        need(not certificate['unconstrained_removed'], 'every coordinate uniquely restored')
        review = engine.verify(parent,child,certificate)
        polynomial = engine.expand(child)
    need((child['metrics']['variables'],child['metrics']['quadratic_rows'],
          child['metrics']['exact_degree'],child['metrics']['expanded_monomials'],
          child['metrics']['max_abs_expanded_coefficient']) == (613,375,4,9661,2445790974704),
         'actual complete expected census')
    files['equation.json'] = encoded(child)
    files['elimination_certificate.json'] = encoded(certificate)
    files['expanded_polynomial.json'] = encoded(polynomial)
    files['BUILD.json'] = encoded(dict(status='PASS',generator_sha256=digest(Path(__file__).read_bytes()),
        configuration=dict(max_support=8,affine_support=None,quadratic_first=False),
        input_literal_sha256=PARENT_EQUATION,metrics=metrics,producer_internal_verification=review,
        sha256={name:digest(data) for name,data in files.items()},
        scope='Separate default-affine raw1493 signed projection. Restore every integer source coordinate and guard first; only then inherit its literal901/nonpointwise904/967 chain. No guard exchange or parent/page/Lean edit.'))
    return files, child['metrics']

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    args = parser.parse_args()
    files, metrics = generate()
    for name,data in files.items():
        target = HERE/name
        if args.check:
            need(target.read_bytes() == data, 'entire deterministic artifact '+name)
        else:
            target.parent.mkdir(parents=True,exist_ok=True)
            target.write_bytes(data)
    print(json.dumps(dict(status='PASS',check=args.check,metrics=metrics),indent=2,sort_keys=True))

if __name__ == '__main__':
    main()

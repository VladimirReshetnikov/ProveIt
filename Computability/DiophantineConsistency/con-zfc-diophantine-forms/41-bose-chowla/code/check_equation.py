#!/usr/bin/env python3
"""Reproduce exact finite certificates for the new fixed polynomial.

Checks definitions, not Con(ZFC) or the existence of an integer zero.
The unbounded equivalence proof is in report.tex and the proof notes.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'upstream/source31/signed10'))
import verify_signed10 as inherited
from circuit import DAG
from build_equation import construct
from shared_powers import power_map
import weights as weights_module


def check_sources():
    manifest = json.loads((ROOT / 'upstream/SOURCE31_MANIFEST.json').read_text())
    for row in manifest['files']:
        raw = (ROOT / 'upstream/source31' / row['path']).read_bytes()
        assert len(raw) == row['bytes']
        assert hashlib.sha256(raw).hexdigest() == row['sha256'], row['path']
        assert hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest() == row['git_blob_sha1']
    return len(manifest['files'])


def check_proof_dependencies():
    manifest = json.loads((ROOT / "upstream/dependencies/DEPENDENCIES_MANIFEST.json").read_text())
    for row in manifest["files"]:
        raw = (ROOT / row["local_path"]).read_bytes()
        assert len(raw) == row["bytes"]
        assert hashlib.sha256(raw).hexdigest() == row["sha256"], row["local_path"]
        assert hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest() == row["git_blob_sha1"]
    return len(manifest["files"])


def check_powers(weights):
    dag = DAG()
    powers = power_map(dag, dag.var('B'), weights)
    exponents = []
    for node in dag.nodes:
        if node['kind'] == 'variable':
            assert node['name'] == 'B'
            exponent = 1
        elif node['kind'] == 'literal':
            assert node['value'] == 1
            exponent = 0
        else:
            assert node['kind'] == 'mul'
            exponent = exponents[node['left']] + exponents[node['right']]
        exponents.append(exponent)
    for expected, node in powers.items():
        assert expected == exponents[node]
    live, todo = set(), list(powers.values())
    while todo:
        i = todo.pop()
        if i in live:
            continue
        live.add(i)
        node = dag.nodes[i]
        if node['kind'] == 'mul':
            todo.extend((node['left'], node['right']))
    return {'target_powers': len(powers), 'multiplications': sum(dag.nodes[i]['kind'] == 'mul' for i in live),
            'proof': 'Every multiplication adds the exact integer exponent labels.'}


def main():
    source_count = check_sources()
    dependency_count = check_proof_dependencies()
    constants, source = inherited.source_coefficients()
    ports, coefficients = inherited.fixed_ports(constants)
    saved_weights = json.loads((ROOT / 'data/weights_certificate.json').read_text())
    reconstructed = weights_module.construct()
    reconstructed.update(weights_module.verify(reconstructed['weights']))
    assert reconstructed == saved_weights
    powers = check_powers(saved_weights['weights'])
    assert powers['multiplications'] == 234
    degree_rows = []
    for literal, filename in [(False, 'equation10.json'), (True, 'equation10_sun_finalizer.json')]:
        expected, _ = construct(literal)
        stored = (ROOT / 'generated' / filename).read_bytes()
        assert stored == (json.dumps(expected, separators=(',', ':')) + '\n').encode(), filename
        degrees = [inherited.degree_certificate(expected, inherited.fixed_leaves(constants, ports, p), p)
                   for p in (101, 1009, 1000003)]
        degree_rows.append({'file': filename, 'sha256': hashlib.sha256(stored).hexdigest(),
                            'degree_certificates': degrees,
                            'operations': sum(expected['operation_counts'].values())})
    assert degree_rows[0]['degree_certificates'][0]['degree'] == 113856 * saved_weights['maximum'] + 27064
    # This inherited helper expands both the norm circuit and all signed factors
    # independently as exact sparse polynomials, then compares them coefficientwise.
    old_root = inherited.ROOT
    inherited.ROOT = ROOT
    try:
        norms = {str(k): len(inherited.norm_polynomial(k)[0]) for k in (3, 4)}
    finally:
        inherited.ROOT = old_root
    receipt = {'status': 'PASS', 'source_files_hashed': source_count, 'proof_dependencies_hashed': dependency_count,
               'source_reconstruction': source, 'fixed_coefficients': coefficients,
               'B4_code': saved_weights, 'shared_powers': powers,
               'exact_norm_term_counts': norms, 'circuits': degree_rows,
               'scope': 'Finite exact arithmetic and transcription checks; the unbounded equivalence is an ordinary proof, not a new proof-assistant build.'}
    (ROOT / 'generated/VERIFICATION.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'status': 'PASS', 'source_files': source_count, 'proof_dependencies': dependency_count,
                      'B4_multisets': saved_weights['multisets_checked'],
                      'degree': degree_rows[0]['degree_certificates'][0]['degree'],
                      'operations': degree_rows[0]['operations'],
                      'coefficient_records': source['weighted_records'],
                      'norm_term_counts': norms}))


if __name__ == '__main__':
    main()

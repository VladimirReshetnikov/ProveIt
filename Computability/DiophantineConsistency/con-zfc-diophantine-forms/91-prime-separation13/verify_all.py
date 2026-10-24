#!/usr/bin/env python3
"""Reproduce the finite certificates; Python standard library only.

This does not decide Con(ZFC), simulate an unbounded machine, or replace
the ordinary soundness/completeness proof in report.pdf and PROOF.md.
All acceptance conditions use explicit exceptions, including under -O.
"""
from pathlib import Path
import argparse
import collections
import gzip
import hashlib
import importlib.util
import json
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
NAMES = {
    13: 'five_root_integer13',
    14: 'four_root_integer14',
    15: 'three_root_integer15',
    16: 'fixed3_crt_integer16',
}
EXPECTED = {
    13: (1392, 205, {'add': 47, 'sub': 28, 'mul': 130}),
    14: (696, 151, {'add': 38, 'sub': 23, 'mul': 90}),
    15: (244, 137, {'add': 33, 'sub': 24, 'mul': 80}),
    16: (108, 132, {'add': 33, 'sub': 24, 'mul': 75}),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def load_module(name, path):
    specification = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    return module


def authenticate_coefficients():
    folder = ROOT / 'new_integer_compression/coefficients'
    binding = json.loads((folder / 'BINDING.json').read_text())
    ports = {}
    raw_total = compressed_total = 0
    for name, entry in binding['payloads'].items():
        compressed = (folder / entry['path']).read_bytes()
        require(sha(compressed) == entry['gzip_sha256'], name + ' compressed SHA-256')
        raw = gzip.decompress(compressed)
        require(sha(raw) == entry['raw_sha256'], name + ' integer SHA-256')
        value = int.from_bytes(raw, 'little')
        require(len(raw) == entry['raw_bytes'], name + ' payload length')
        require(value.bit_length() == entry['bits'], name + ' bit length')
        require(len(raw) == (value.bit_length() + 7) // 8, name + ' minimal encoding')
        ports[name] = value
        raw_total += len(raw)
        compressed_total += len(compressed)
    require(raw_total == binding['total_raw_bytes'] == 615883, 'total integer bytes')
    require(compressed_total == binding['total_compressed_bytes'] == 10607,
            'total compressed integer bytes')
    require(ports['beta'] == (1 << 1064921) - 1, 'exact beta')
    require(ports['cone_A'] == 1 << 1113, 'exact first determinant scale')
    require(ports['cone_B'] == 1 << 666104, 'exact second determinant scale')
    recipe = load_module('coefficient_recipe_checked', ROOT / 'coefficient_recipe/build_coefficients.py')
    constructed, receipt = recipe.construct()
    for external, native in [('beta', 'beta'), ('K0', 'K'), ('MC', 'MC'), ('MF', 'MF_source')]:
        require(ports[external] == constructed[native], 'coherent source-34 coefficient ' + external)
    return {'status': 'PASS', 'ports': sorted(ports), 'raw_bytes': raw_total,
            'gzip_bytes': compressed_total, 'all_six_payload_hashes_checked': True,
            'full_native_tuple_regenerated_from_literal_machine_and_tiles': True,
            'MF_convention': 'already shifted by beta', 'finite_recipe_checks': receipt}


def check_dag(packet):
    variables = packet['variables']; ports = packet['fixed_ports']
    require(len(variables) == packet['variable_count'] == len(set(variables)), 'variable count')
    require(set(variables).isdisjoint(ports), 'input classes disjoint')
    known = {'v:' + x for x in variables} | {'c:' + x for x in ports}
    table = {}
    fixed_ids = set()
    def valid_reference(token):
        if token.startswith('n:'):
            require(str(int(token[2:])) == token[2:], 'canonical integer literal')
        else:
            require(token in known, 'forward or hidden reference ' + token)
    for node in packet['fixed_recipes'] + packet['nodes']:
        require(node['op'] in ('add', 'sub', 'mul'), 'binary polynomial gate')
        require(node['id'] not in known, 'unique gate identifier')
        valid_reference(node['left']); valid_reference(node['right'])
        known.add(node['id']); table[node['id']] = node
    for node in packet['fixed_recipes']:
        for key in ('left', 'right'):
            ref = node[key]
            require(ref.startswith(('n:', 'c:')) or ref in fixed_ids, 'fixed-only recipe')
        fixed_ids.add(node['id'])
    valid_reference(packet['output'])
    live = set()
    def visit(token):
        if token in live:
            return
        live.add(token)
        if token in table:
            visit(table[token]['left']); visit(table[token]['right'])
    visit(packet['output'])
    require(all('v:' + x in live for x in variables), 'all quantified coordinates live')
    require(all(node['id'] in live for node in packet['nodes']), 'no counted dead variable gate')
    histogram = dict(collections.Counter(n['op'] for n in packet['nodes']))
    require(len(packet['nodes']) == packet['operation_count'], 'actual operation count')
    require(histogram == packet['operation_histogram'], 'actual operation histogram')
    return {'declared_and_live_variables': len(variables), 'fixed_ports': len(ports),
            'live_binary_operations': len(packet['nodes']), 'histogram': histogram,
            'acyclic': True, 'only_integer_constants_add_sub_mul': True}


def reproduce_circuits():
    sys.path.insert(0, str(ROOT / 'new_integer_compression'))
    dense = load_module('reference_builder_checked', ROOT / 'new_integer_compression/build.py')
    compact = load_module('compact_builder_checked', ROOT / 'new_integer_compact/build.py')
    results = []
    with tempfile.TemporaryDirectory(prefix='con_zfc_prime_') as temporary:
        temporary = Path(temporary)
        dense.ROOT = temporary / 'dense'; dense.ROOT.mkdir()
        compact.ROOT = temporary / 'compact'; compact.ROOT.mkdir()
        for n, name in NAMES.items():
            dense.build(n); compact.build(n)
            for folder, regenerated, filename in [
                ('new_integer_compression', dense.ROOT, name + '.json'),
                ('new_integer_compact', compact.ROOT, name + '_compact.json')]:
                original = ROOT / folder / filename
                require(original.read_bytes() == (regenerated / filename).read_bytes(),
                        'byte-identical regenerated packet ' + filename)
                packet = json.loads(original.read_text())
                topology = check_dag(packet)
                if folder == 'new_integer_compact':
                    degree, operations, histogram = EXPECTED[n]
                    require(packet['exact_total_degree'] == degree, 'declared degree')
                    require(packet['operation_count'] == operations, 'primary gate record')
                    require(packet['operation_histogram'] == histogram, 'primary gate histogram')
                results.append({'file': folder + '/' + filename,
                                'sha256': sha(original.read_bytes()), 'rebuild': 'byte-identical',
                                'topology': topology})
    return results


def check_norms_and_degrees():
    audit = load_module('independent_norm_audit_checked', ROOT / 'independent_audit/check_compact_norms.py')
    degrees = load_module('degree_certificate_checked', ROOT / 'new_integer_compression/check_degrees.py')
    primary = load_module('primary_formula_checked', ROOT / 'independent_audit/check_primary_formula.py').verify_all()
    universal = audit.universal_identity_checks()
    quadratic = audit.quadratic_algebra_checks()
    literal = audit.compare_literals()
    specialized = audit.degree_specialization_checks()
    archived = json.loads((ROOT / 'new_integer_compression/DEGREE_LOWER_CERTIFICATES.json').read_text())
    reproduced = [degrees.run(ROOT / 'new_integer_compression' / (NAMES[n] + '.json'))
                  for n in (16, 15, 14, 13)]
    require(reproduced == archived, 'complete degree certificate reproduction')
    return {'primary_formula_exact_gate_binding': primary, 'universal_norm_identities': universal, 'universal_quadratic_identities': quadratic,
            'literal_modular_diagnostics': literal, 'independent_full_specializations': specialized,
            'reference_degree_certificates_reproduced': reproduced,
            'scope': 'Universal identities are exact integer polynomial identities. Modular diagnostics detect transcription errors. Nonzero finite-field leading coefficients certify lower bounds; the ordinary degree analysis supplies upper bounds.'}


def check_manifest():
    path = ROOT / 'SHA256SUMS.txt'
    if not path.exists():
        return {'status': 'not yet generated during package assembly'}
    count = 0
    for line in path.read_text().splitlines():
        expected, relative = line.split('  ', 1)
        file = ROOT / relative
        require(file.is_relative_to(ROOT) and '..' not in Path(relative).parts, 'safe manifest path')
        require(file.is_file() and sha(file.read_bytes()) == expected, 'manifest ' + relative)
        count += 1
    return {'status': 'PASS', 'files': count}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT / 'VERIFICATION_LAST_RUN.json')
    args = parser.parse_args()
    result = {'status': 'RUNNING', 'python': sys.version.split()[0], 'optimized_mode': not __debug__,
              'scope': 'Finite construction and algebra certificate replay; not a formal proof of the entire inherited calibration.'}
    for key, function in [('coefficients', authenticate_coefficients),
                          ('circuit_reproduction', reproduce_circuits),
                          ('norm_and_degree_audit', check_norms_and_degrees)]:
        print('Checking ' + key + '...', flush=True)
        result[key] = function()
    ancillary = ROOT / 'ten_integer/verify.py'
    if ancillary.exists():
        module = load_module('ten_integer_verifier_checked', ancillary)
        if hasattr(module, 'verify_all'):
            print('Checking ten_integer identities...', flush=True)
            result['ten_integer'] = module.verify_all()
    result['manifest'] = check_manifest()
    result['status'] = 'PASS'
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print('PASS: six fixed integers regenerated; eight polynomial circuits reproduced; exact norm identities and four total-degree certificates checked.')
    print('Receipt: ' + str(args.output))


if __name__ == '__main__':
    main()

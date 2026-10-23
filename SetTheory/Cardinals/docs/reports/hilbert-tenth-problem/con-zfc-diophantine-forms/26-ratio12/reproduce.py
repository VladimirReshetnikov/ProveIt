#!/usr/bin/env python3
"""Rebuild and check this package offline, using Python 3.10+ standard library.

This verifies finite circuits, fixtures, layout calculations and fixed bytes.
It does not decide Diophantine solvability or formalize the mathematical proof.
Run from any directory: python3 -B /path/to/this/package/reproduce.py
"""
from pathlib import Path
import gzip
import hashlib
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
VERIFICATION = ROOT / 'verification'
SOURCE_COMMIT = 'a477d0fc8b6feda53796835564a988015e744d4d'
VARIANT = 'wang943-parity-H1-5pow10'
PORTS = {'beta': 'beta', 'K0': 'K', 'MC': 'MC', 'MF': 'MF_source'}
# unknowns, operations, multiplications, additions/subtractions, residual degrees
EXPECTED = {
    'ratio12_product': (12, 116, 74, 42, [1081]),
    'ratio12_system': (12, 111, 72, 39, [7, 2, 1072]),
    'ratio12_system_shifted': (12, 110, 72, 38, [7, 2, 1072]),
    'integer24_product': (24, 163, 94, 69, [2432]),
    'integer24_system': (24, 159, 92, 67, [12, 4, 2416]),
    'integer24_system_shifted': (24, 157, 92, 65, [12, 4, 2416]),
    'integer24_sos': (24, 166, 95, 71, [4832]),
}
FROZEN_RAW_HASHES = {
    'beta': '40cc309fcb5dd2942c371d18be6d955d472e6b4c3604034b316194037ac16a5d',
    'K': 'a36a9c74cfd6b9f7eb814788697f0bb03ff262ba352de01eed4a8ad0af82bd59',
    'MC': 'a568d4390184175a90a519ba06f8c222bd8ed9bb68fe55a670ed3edebaf9dcf9',
    'MF_source': '38994876c29f1140dedce9ad8a6b51b718a2418025a0c80ba715533bd59cf1af',
}
SCRIPTS = [
    'arithmetic/build_ratio12.py',
    'arithmetic/build24.py',
    'verification/audit_new_circuits.py',
    'coefficients/reproduce_coefficients.py',
]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_json(path):
    return json.loads(path.read_text(encoding='utf-8'))


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def run_script(relative):
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    env.pop('PYTHONOPTIMIZE', None)  # The supplied diagnostic scripts use assert.
    run = subprocess.run([sys.executable, '-B', str(ROOT / relative)], cwd=ROOT,
                         env=env, capture_output=True, text=True)
    log = VERIFICATION / (Path(relative).stem + '.log')
    log.write_text(run.stdout + run.stderr, encoding='utf-8')
    require(run.returncode == 0,
            '{} failed (exit {}); see {}'.format(relative, run.returncode, log))
    print('PASS ' + relative, flush=True)
    return {'script': relative, 'exit_code': 0,
            'log': str(log.relative_to(ROOT))}


def check_circuits():
    independent = read_json(VERIFICATION / 'INDEPENDENT_CIRCUIT_CHECKS.json')
    rows = {Path(row['path']).stem: row for row in independent['packets']}
    require(set(rows) == set(EXPECTED), 'Unexpected independent circuit set')
    require(independent[
        'integer24_product_suffix_identical_to_independently_fetched_package21'],
        'Inherited package-21 arithmetic core differs')
    result = []
    for name, (unknowns, ops, muls, adds, degrees) in EXPECTED.items():
        row = rows[name]
        packet_path = ROOT / 'arithmetic' / (name + '.json')
        packet = read_json(packet_path)
        for key, wanted in [('unknowns', unknowns), ('operations', ops),
                            ('multiplications', muls),
                            ('additions_subtractions', adds)]:
            require(row[key] == wanted, '{}: incorrect {}'.format(name, key))
        require(row['syntactic_residual_degree_upper_bounds'] == degrees,
                name + ': unexpected syntactic residual degrees')
        require(row['sha256'] == sha256(packet_path.read_bytes()),
                name + ': audit did not inspect the current packet')
        require(packet['fixed_numerals'] == list(PORTS),
                name + ': wrong fixed coefficient ports')
        target = (packet_path.parent / packet['coefficient_binding']).resolve()
        require(target == ROOT / 'coefficients' / 'COEFFICIENT_BINDING.json',
                name + ': coefficient binding does not resolve')
        require(packet['domain'] == ('strictly positive integers' if unknowns == 12
                                     else 'unrestricted integers'),
                name + ': wrong witness domain')
        if 'comparisons' in packet:
            require(packet['residual_exact_degrees'] == degrees,
                    name + ': wrong exact-degree declaration')
        else:
            require(packet['exact_degree'] == degrees[0],
                    name + ': wrong exact-degree declaration')
        if unknowns == 24:
            require(packet['proof'].startswith('../report.tex,'),
                    name + ': incorrect proof path')
        else:
            require(packet['source_provenance']['commit'] == SOURCE_COMMIT,
                    name + ': incorrect source commit')
        result.append({'id': name, 'unknowns': unknowns, 'equations': len(degrees),
                       'operations': ops, 'multiplications': muls,
                       'additions_subtractions': adds,
                       'residual_degree_upper_bounds': degrees,
                       'sha256': row['sha256']})
    return result


def check_binding():
    base = ROOT / 'coefficients'
    wrapper = read_json(base / 'COEFFICIENT_BINDING.json')
    canonical_path = (base / wrapper['canonical_binding']).resolve()
    require(canonical_path == base / 'compiler' / 'COEFFICIENT_BINDING.json',
            'Wrong canonical coefficient-binding path')
    canonical = read_json(canonical_path)
    require(wrapper['variant'] == canonical['variant'] == VARIANT,
            'Coefficient variants disagree')
    require(canonical['source_revision'] == SOURCE_COMMIT,
            'Coefficient provenance commit differs')
    for binding in (wrapper, canonical):
        require(all(binding['circuit_port_aliases'].get(k) == v
                    for k, v in PORTS.items()), 'Fixed-port alias mismatch')
    canonical_rows = {r['name']: r for r in canonical['files']}
    wrapper_rows = {r['name']: r for r in wrapper['files']}
    require(set(canonical_rows) == set(wrapper_rows) == set(FROZEN_RAW_HASHES),
            'Coefficient tuple must contain exactly four fixed integers')
    values, raw_total, compressed_total = {}, 0, 0
    for name, frozen in FROZEN_RAW_HASHES.items():
        row, c = wrapper_rows[name], canonical_rows[name]
        path = (base / row['path']).resolve()
        require(path == (base / wrapper['source_bindings'][name]).resolve(),
                name + ': wrapper source path mismatch')
        require(path == (canonical_path.parent /
                         canonical['source_bindings'][name]).resolve(),
                name + ': canonical source path mismatch')
        compressed = path.read_bytes()
        require(len(compressed) == row['bytes'] == c['gzip_bytes'],
                name + ': compressed size mismatch')
        require(sha256(compressed) == row['sha256'] == c['gzip_sha256'],
                name + ': compressed hash mismatch')
        raw = gzip.decompress(compressed)
        u = row['uncompressed']
        require(sha256(raw) == frozen == u['sha256'] == c['sha256'],
                name + ': frozen integer hash mismatch')
        require(len(raw) == u['bytes'] == c['bytes'] and raw[-1] != 0,
                name + ': nonminimal or incorrect integer byte length')
        value = int.from_bytes(raw, 'little')
        require(value.bit_length() == u['bit_length'] == c['bit_length'],
                name + ': bit length mismatch')
        require(value.bit_count() == u['population'] == c['population'],
                name + ': population mismatch')
        values[name] = value
        raw_total += len(raw)
        compressed_total += len(compressed)
    require(raw_total == 4882894 == wrapper['total_uncompressed_bytes'],
            'Wrong total raw coefficient bytes')
    require(compressed_total == 19820 == wrapper['total_gzip_bytes'],
            'Wrong total compressed coefficient bytes')
    beta, K, MC, MF_source = (values[n] for n in ('beta', 'K', 'MC', 'MF_source'))
    d = 5**10
    require(beta + 1 == 1 << d, 'Wrong fixed base')
    DC, DR = K & beta, K >> d
    MF_native = MF_source - beta
    require(DR == 1 << 625 and (2*DC-DR) % 5 == 3,
            'Compiler shift or 5-adic unit differs')
    require(MC.bit_count() == 9764636 and MF_native.bit_count() == 989,
            'Compiler mask populations differ')
    require(K.bit_length() == 9766251, 'Wrong largest coefficient bit length')
    replay = read_json(base / 'COEFFICIENT_REPLAY.json')
    require(replay['status'] == 'PASS' and len(replay['runs']) == 6,
            'Coefficient replay incomplete')
    for relative in ('audit/PARITY_INDEPENDENT_CHECKS.json',
                     'audit/PARITY_CROSS_AGENT_CHECKS.json'):
        receipt = read_json(base / relative)
        require(receipt['status'] == 'PASS' and
                receipt['basis_convolution_checks'] == 69230,
                'Independent coefficient audit incomplete: ' + relative)
    return {'variant': VARIANT, 'ports': PORTS, 'fixed_ports': 4,
            'all_compressed_and_uncompressed_hashes_match': True,
            'largest_port_bits': 9766251, 'raw_payload_bytes': raw_total,
            'gzip_payload_bytes': compressed_total,
            'coefficient_scripts_passed': 6,
            'basis_checks_per_independent_coefficient_audit': 69230}


def check_results():
    results = read_json(ROOT / 'RESULTS.json')
    require(results['source_commit'] == SOURCE_COMMIT,
            'RESULTS provenance differs')
    rows = {r['id']: r for r in results['constructions']}
    require(set(rows) == set(EXPECTED), 'RESULTS construction list differs')
    for name, (unknowns, ops, _m, _a, degrees) in EXPECTED.items():
        row = rows[name]
        require(row['unknowns'] == unknowns and row['operations'] == ops and
                row['equations'] == len(degrees) and
                row['max_degree'] == max(degrees), name + ': RESULTS mismatch')
        require(row['circuit'] == 'arithmetic/' + name + '.json',
                name + ': incorrect RESULTS circuit path')
    backend = results['coefficient_backend']
    require(backend['variant'] == VARIANT and backend['max_port_bits'] == 9766251
            and backend['raw_payload_bytes'] == 4882894
            and backend['gzip_payload_bytes'] == 19820,
            'RESULTS coefficient metrics differ')


def check_diagnostics():
    positive = read_json(ROOT / 'arithmetic' / 'ratio12_checks.json')
    integer = read_json(ROOT / 'arithmetic' / 'CHECKS24.json')
    checks = integer['checks']
    require(integer['source_commit'] == SOURCE_COMMIT,
            'Integer diagnostic source commit differs')
    require(positive['exact_conjugate_product_signed_fixtures'] == 40 and
            len(positive['isolated_rational_inverse_fixtures']) == 18 and
            all(row['inverse_exact'] for row in
                positive['isolated_rational_inverse_fixtures']),
            'Positive-circuit finite diagnostics incomplete')
    require(checks['exact_norm_and_substitution_fixtures'] == 32 and
            checks['signed_boundary_fixtures'] == 36 and
            checks['shifted_system_exact_fixtures'] == 32,
            'Integer-circuit finite diagnostics incomplete')
    require(len(positive['modular_leading_form_diagnostics']) == 2 and
            len(checks['leading_form_modular_diagnostics']) == 2,
            'Leading-form finite diagnostics incomplete')
    return {'ratio12_exact_norm_fixtures': 40,
            'ratio12_exact_rational_inverse_fixtures': 18,
            'integer24_exact_norm_and_substitution_fixtures': 32,
            'integer24_signed_boundary_fixtures': 36,
            'integer24_shifted_system_fixtures': 32,
            'modular_leading_form_diagnostics_per_family': 2}


def main():
    require(sys.version_info >= (3, 10), 'Python 3.10 or newer is required')
    VERIFICATION.mkdir(exist_ok=True)
    runs = [run_script(script) for script in SCRIPTS]
    circuits = check_circuits()
    binding = check_binding()
    diagnostics = check_diagnostics()
    check_results()
    receipt = {
        'status': 'PASS', 'source_commit': SOURCE_COMMIT,
        'python_version': '.'.join(map(str, sys.version_info[:3])),
        'runs': runs, 'circuits': circuits, 'coefficient_binding': binding,
        'finite_diagnostics': diagnostics,
        'results_summary_matches': True,
        'scope': ('Finite arithmetic, independent circuit ledgers, concrete '
                  'coefficient geometry, and fixed bytes only. Exact degree '
                  'lower bounds and unbounded equivalences are ordinary '
                  'mathematical proofs in report.tex and proofs/. No claim of '
                  'an end-to-end proof-assistant verification or a decision '
                  'of Diophantine solvability is made.'),
    }
    (VERIFICATION / 'REPRODUCTION.json').write_text(
        json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
    print('PASS: 7 circuits, 4 fixed coefficient ports, 6 coefficient scripts.')
    print('Receipt: verification/REPRODUCTION.json')


if __name__ == '__main__':
    main()

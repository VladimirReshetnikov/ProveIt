#!/usr/bin/env python3
"""Verify the supplied package offline, using only Python's standard library.

Usage:
    python3 verify.py
    python3 verify.py --receipt evidence/FINAL_VERIFICATION.json

The default receipt is relative to this package, independent of the current
working directory. No supplied circuit or coefficient payload is changed.
Audit receipts are refreshed. Finite-field checks are diagnostics; they do
not replace the report's uniform polynomial, Pell, compiler or ZFC proofs.
Requires Python 3.10 or later. Every check remains active under python -O.
"""
import argparse
import gzip
import importlib.util
import json
from pathlib import Path
import random
import subprocess
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT/'code'))
from circuit_tools import (PORTS, audit_dag, digest, evaluate, normalized_ports,
                           require, residual_values, source_digest)
from degree_check import diagnostic
from refactor_comparison_circuits import refactor_norm, refactor_monic
from bind_coefficients import SOURCE_MAP
from build_coefficients import recipe, check_geometry, check_padding

PIN = 'ae3007ca4467011e0e051c84acb4a1dd13971b0e'
INSTANCE = 'wang943-minodd-529x12031'
FIELDS = [(1000000007, 215), (1000000009, 216)]
# (witnesses, exact residual degrees or polynomial degree, multiplications,
#  additions/subtractions). Literal-scalar multiplications are counted.
EXPECTED = {
    'baseline67': (15, 155, 39, 28),
    'retained59_system': (16, [22, 18, 24, 7, 2, 22, 6], 33, 26),
    'optimized_norm12_product': (12, 1353, 70, 43),
    'optimized_norm12_system': (12, [7, 2, 1344], 68, 40),
    'optimized_merger12_product': (12, 1529, 70, 44),
    'optimized_merger12_system': (12, [7, 2, 1520], 68, 41),
    'optimized_merger13_product': (13, 319, 51, 38),
    'optimized_merger13_system': (13, [7, 2, 22, 288], 48, 33),
    'optimized_separating_saturated12_product': (12, 1081, 77, 43),
    'optimized_separating_saturated12_system': (12, [7, 2, 1072], 75, 40),
    'optimized_separating_saturated12_sos': (12, 2144, 78, 45),
    'optimized_tight_separating12_product': (12, 1073, 77, 44),
    'optimized_tight_separating12_system': (12, [7, 2, 1064], 75, 41),
    'optimized_tight_separating12_sos': (12, 2128, 78, 46),
    'optimized_tightest_separating12_product': (12, 1069, 78, 45),
    'optimized_tightest_separating12_system': (12, [7, 2, 1060], 76, 42),
    'optimized_tightest_separating12_sos': (12, 2120, 79, 47),
    'signed_separating_saturated24_product': (24, 1936, 100, 67),
    'signed_separating_saturated24_system': (24, [12, 4, 1920], 98, 64),
    'signed_separating_saturated24_sos': (24, 3840, 101, 69)}
RAW_HASHES = {
    'beta': '77d7cab405c98819e1cafb9b567c306aaf9ddba369b6dda4507d34d1690db6c9',
    'K0': '273bdb45a0493a0e3dc548777984d9184733065240648f90ff70ea1a000bcff3',
    'MC': 'ccb88e64f7b2e83eb8c8798b29dcbd3ff76a721255fdbc32f5c7c5066707af0c',
    'MF': 'e3f95e43a4d315b34bb9b580d3ef11ae752699c86816cb726245a3a5f7b47915'}
CORE_BUILDERS = ['build_optimized_1069.py', 'build_optimized_1073.py',
                 'build_optimized_1081.py', 'build_signed24.py']


def local(path, base=ROOT):
    result = (base/path).resolve()
    require(result == ROOT or ROOT in result.parents, 'path escapes package: ' + str(path))
    return result


def read_json(path):
    return json.loads(path.read_text())


def provenance():
    pins = read_json(ROOT/'evidence/SOURCE_PINS.json')
    require(pins['repository'] == 'VladimirReshetnikov/ProveIt' and pins['commit'] == PIN,
            'unexpected upstream identity')
    rows = pins['files']
    require(len(rows) == 28 and len({r['local_path'] for r in rows}) == 28,
            'source pin inventory mismatch')
    for row in rows:
        require(digest(local(row['local_path']).read_bytes()) == row['sha256'],
                'upstream digest mismatch: ' + row['local_path'])
    by_path = {r['local_path']: r for r in rows}
    baseline = read_json(ROOT/'evidence/BASELINE_PROVENANCE.json')
    require(len(baseline) == 6, 'comparison provenance inventory mismatch')
    for row in baseline:
        pin = by_path[row['local_path']]
        require(row['commit'] == PIN and row['sha256'] == pin['sha256']
                and row['source_path'] == pin['repository_path'],
                'comparison provenance differs from primary pin')
    return by_path


def coefficients():
    path = ROOT/'coefficients/COEFFICIENT_BINDING.json'
    binding = read_json(path)
    require(binding['instance'] == INSTANCE and binding['source_commit'] == PIN,
            'unexpected coefficient instance')
    require(binding['radix_bits'] == 529 and binding['cell_length'] == 12031
            and binding['d'] == 6364399 and binding['tiles'] == 943,
            'unexpected coefficient recipe parameters')
    require([r['port'] for r in binding['files']] == PORTS, 'incomplete tuple')
    values = {}
    for row in binding['files']:
        compressed = local(row['file'], path.parent).read_bytes()
        raw = gzip.decompress(compressed)
        require(len(compressed) == row['gzip_bytes']
                and digest(compressed) == row['gzip_sha256'], 'gzip payload mismatch')
        require(len(raw) == row['bytes'] and raw and raw[-1] != 0,
                'nonminimal or wrong-size coefficient')
        require(digest(raw) == row['sha256'] == RAW_HASHES[row['port']],
                'materialized numeral differs from the fixed instance')
        values[row['port']] = int.from_bytes(raw, 'little')
        require(values[row['port']].bit_length() == row['bits'], 'coefficient bit mismatch')
    require(values['beta'] + 1 == 1 << binding['d'], 'wrong beta numeral')
    return binding, digest(path.read_bytes()), values


def packet_audits(binding, binding_hash, pins):
    files = sorted((ROOT/'circuits').glob('*.json'))
    require({p.stem for p in files} == set(EXPECTED), 'circuit inventory mismatch')
    index = read_json(ROOT/'evidence/CIRCUIT_INDEX.json')
    require(index['status'] == 'PASS' and index['circuit_count'] == len(EXPECTED)
            and index['coefficient_instance'] == INSTANCE
            and index['coefficient_binding_sha256'] == binding_hash,
            'stale circuit index')
    indexed = {r['file']: r for r in index['circuits']}
    require(len(indexed) == len(EXPECTED), 'duplicate circuit index entry')
    packets, records = {}, []
    for path in files:
        p = read_json(path)
        require(p['name'] == path.stem, 'circuit name differs from filename')
        n, degrees, muls, adds = EXPECTED[p['name']]
        require(p['fixed_numerals'] == PORTS and len(p['witnesses']) == n,
                'circuit interface mismatch')
        domain = 'unrestricted integers' if n == 24 else 'strictly positive integers'
        require(p['domain'] == domain, 'wrong witness domain')
        degree = p.get('exact_degree', p.get('residual_exact_degrees'))
        require(degree == degrees, 'stale degree claim')
        if isinstance(degrees, list):
            require(len(p['comparisons']) == len(degrees)
                    and p['exact_maximum_degree'] == max(degrees), 'wrong residual ledger')
        ledger = audit_dag(p)
        require(p['ledger'] == ledger, 'DAG ledger or liveness claim is stale')
        require(ledger['multiplications'] == muls
                and ledger['additions_subtractions'] == adds, 'unexpected operation count')
        require(p['source_sha256'] == source_digest(p['source']), 'source DAG digest mismatch')
        require(p['coefficient_binding'] == '../coefficients/COEFFICIENT_BINDING.json'
                and local(p['coefficient_binding'], path.parent) == ROOT/'coefficients/COEFFICIENT_BINDING.json'
                and p['coefficient_binding_sha256'] == binding_hash
                and p['coefficient_instance'] == INSTANCE
                and p['coefficient_payload_sha256'] == RAW_HASHES,
                'circuit is not bound to the complete current tuple')
        require(p['proof_reference'] == '../con_zfc_synthesis.tex'
                and local(p['proof_reference'], path.parent).is_file(), 'proof source pointer is stale')
        if p['name'] in SOURCE_MAP:
            source = p['preserved_source']
            source_path = 'upstream/' + SOURCE_MAP[p['name']]
            require(local(source['path'], path.parent) == ROOT/source_path
                    and source['sha256'] == pins[source_path]['sha256']
                    and source['repository_path'] == pins[source_path]['repository_path']
                    and source['commit'] == PIN, 'preserved-source pointer mismatch')
        else:
            require(local(p['builder'], path.parent).name in CORE_BUILDERS, 'unknown core builder')
        relative = str(path.relative_to(ROOT))
        actual = dict(file=relative, sha256=digest(path.read_bytes()), variables=n,
                      domain=domain, equations=len(degrees) if isinstance(degrees, list) else 1,
                      degree=max(degrees) if isinstance(degrees, list) else degrees,
                      operations=muls+adds, source_sha256=p['source_sha256'])
        require(indexed.get(relative) == actual, 'circuit index packet mismatch')
        records.append(actual)
        packets[p['name']] = p
    return packets, records


def arithmetic_reproduction(packets):
    """Check every supplied gate list against its deterministic constructor."""
    for name, source in SOURCE_MAP.items():
        original = read_json(ROOT/'upstream'/source)
        q = (refactor_norm(original) if name.startswith('optimized_norm') else
             refactor_monic(original) if name.startswith('optimized_merger') else original)
        q = normalized_ports(q)
        for key in ['source', 'witnesses', 'fixed_numerals', 'output', 'comparisons']:
            require(q.get(key) == packets[name].get(key), 'refactor reconstruction mismatch: ' + name)
    reconstructed = len(SOURCE_MAP)
    for filename in CORE_BUILDERS:
        spec = importlib.util.spec_from_file_location('_verify_' + filename[:-3], ROOT/'code'/filename)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        generated = module.construct()
        if filename == 'build_signed24.py':
            generated = [module.lift24(p) for p in generated]
        for q in generated:
            for key in ['source', 'witnesses', 'fixed_numerals', 'output', 'comparisons',
                        'domain', 'exact_degree', 'residual_exact_degrees']:
                require(q.get(key) == packets[q['name']].get(key), 'core reconstruction mismatch: ' + q['name'])
            reconstructed += 1
    require(reconstructed == 20, 'not every delivered DAG was reconstructed')
    return reconstructed


def run_audit(filename):
    run = subprocess.run([sys.executable, '-B', str(ROOT/'code'/filename)],
                         cwd=ROOT, capture_output=True, text=True)
    require(run.returncode == 0, filename + ' failed:\n' + run.stdout + run.stderr)
    result = json.loads(run.stdout)
    require(result['status'] == 'PASS', filename + ' did not report PASS')
    return result


def upstream_comparisons(packets, values):
    records = []
    for name, source in SOURCE_MAP.items():
        original = normalized_ports(read_json(ROOT/'upstream'/source))
        q = packets[name]
        require(original['witnesses'] == q['witnesses'], 'source witness order changed')
        for prime, seed in FIELDS:
            rng = random.Random(seed)
            coeff = {n: values[n] % prime for n in PORTS}
            for case in range(64):
                # Include zero and two constant assignments, then signed fixtures.
                witness = {n: case-1 if case < 3 else rng.randrange(-prime, prime)
                           for n in q['witnesses']}
                point = dict(coeff, **witness)
                require(residual_values(original, point, prime) == residual_values(q, point, prime),
                        'upstream polynomial/residual comparison failed: ' + name)
        records.append(dict(name=name, preserved_source='upstream/'+source,
                            primes=[x[0] for x in FIELDS], cases_per_prime=64,
                            complete_actual_coefficient_residues=True))
    return records


def direct_conjugate_norm(a, prime):
    """Independent multiplication in a three-generator quadratic quotient."""
    radicals = [a['G'], a['A'], a['D']]
    def product(x, y):
        z = [0]*8
        for i, u in enumerate(x):
            for j, v in enumerate(y):
                factor = 1
                for bit, square in enumerate(radicals):
                    if i & j & (1 << bit):
                        factor = factor*square % prime
                z[i ^ j] = (z[i ^ j]+factor*u*v) % prime
        return z
    acc = [1]+[0]*7
    for sg in [-1, 1]:
        for sa in [-1, 1]:
            for sd in [-1, 1]:
                root = [a['S'], sg*a['L'], sa*a['m'], 0, 0, 0, 0, 0]
                factor = [a['d']*x % prime for x in product(root, root)]
                factor[0] = (factor[0]-a['H']**2*a['e']) % prime
                factor[4] = sd*a['H']**2*2*a['Q']*a['v']*a['b'] % prime
                acc = product(acc, factor)
    require(not any(acc[1:]), 'conjugate product did not descend to scalars')
    return acc[0]


def core_norm_checks(packets, values):
    families = ['optimized_tightest_separating12', 'optimized_tight_separating12',
                'optimized_separating_saturated12', 'signed_separating_saturated24']
    for family in families:
        p, s, sos = [packets[family+'_'+suffix] for suffix in ['product', 'system', 'sos']]
        for prime, seed in FIELDS:
            rng = random.Random(seed+1936)
            coeff = {n: values[n] % prime for n in PORTS}
            for _ in range(16):
                point = dict(coeff, **{n: rng.randrange(-prime, prime) for n in p['witnesses']})
                a = evaluate(p, point, prime)
                norm = direct_conjugate_norm(a, prime)
                require(a['N'] == norm, 'eight-conjugate comparison failed')
                require(a[p['output']] == (a['Nk']*a['Nt']*(1+norm)-1) % prime,
                        'product wrapper mismatch')
                require(residual_values(s, point, prime) == [(a['Nk']-1) % prime,
                        (a['Nt']-1) % prime, norm], 'system wrapper mismatch')
                require(residual_values(sos, point, prime) == [
                        ((a['Nk']-1)**2+(a['Nt']-1)**2+norm*norm) % prime], 'SOS wrapper mismatch')
    return dict(families=len(families), primes=[x[0] for x in FIELDS],
                cases_per_family_per_prime=16, eight_conjugate_products=128,
                complete_actual_coefficient_residues=True,
                scope='Finite arithmetic comparisons, separate from the exact symbolic identities.')


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--receipt', default='evidence/FINAL_VERIFICATION.json',
                        help='receipt path relative to the package (default: %(default)s)')
    args = parser.parse_args()
    pins = provenance()
    binding, binding_hash, values = coefficients()
    recipe_data = recipe()
    geometry = check_geometry(recipe_data)
    padding = check_padding(recipe_data[-2])
    require(geometry == binding['geometry'] and padding == binding['padding'],
            'coefficient geometry or padding receipt differs from recomputation')
    packets, records = packet_audits(binding, binding_hash, pins)
    reconstructed = arithmetic_reproduction(packets)
    audits = {name: run_audit(name) for name in [
        'audit_materialized_coefficients.py', 'check_exact_identities.py', 'check_signed24_leading.py']}
    comparisons = upstream_comparisons(packets, values)
    core = core_norm_checks(packets, values)
    degrees = [diagnostic(packets[name], prime, seed, coefficient_values=values)
               for name in sorted(packets) for prime, seed in FIELDS]
    signed_degrees = [r for r in degrees if r['name'] == 'signed_separating_saturated24_product']
    (ROOT/'evidence/signed24_full_degree_checks.json').write_text(json.dumps(dict(
        scope='Complete actual materialized coefficient tuple; exact full finite-field univariate diagnostics, separate from the uniform degree proof.',
        coefficient_binding_sha256=binding_hash, records=signed_degrees), indent=2)+'\n')
    result = dict(status='PASS', source_commit=PIN, coefficient_instance=INSTANCE,
        coefficient_binding_sha256=binding_hash,
        scope='Offline integrity, exact integer-polynomial identity checks, structural DAG reconstruction, and finite arithmetic diagnostics. The ordinary mathematical proofs in the report are still required; this is not a Lean/Rocq proof of the compiler or of Con(ZFC).',
        preserved_source_files=len(pins), coefficient_payloads=binding['files'],
        coefficient_geometry_audit=geometry, coefficient_padding_audit=padding,
        actual_coefficient_residues={str(p): {n: values[n] % p for n in PORTS} for p, _ in FIELDS},
        circuit_count=len(packets), reconstructed_gate_lists=reconstructed, circuits=records,
        independent_coefficient_audit=audits['audit_materialized_coefficients.py'],
        exact_polynomial_identities=audits['check_exact_identities.py'],
        signed_leading_formula_diagnostic=audits['check_signed24_leading.py'],
        preserved_original_comparisons=comparisons, core_conjugate_diagnostics=core,
        full_finite_field_degree_checks=degrees,
        degree_scope='Each record evaluates the complete univariate polynomial over a finite field with all four residues read from the actual coefficient payloads. A nonzero top term certifies the corresponding lower bound. The uniform upper bounds, including cancellations, are proved separately in the report.')
    receipt = local(args.receipt)
    receipt.parent.mkdir(parents=True, exist_ok=True)
    receipt.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(status='PASS', preserved_source_files=len(pins),
        materialized_coefficients=len(values), circuits=len(packets), reconstructed_gate_lists=reconstructed,
        coefficient_basis_convolution_checks=geometry['basis_convolution_checks'],
        preserved_original_comparison_cases=len(comparisons)*128,
        direct_conjugate_comparisons=core['eight_conjugate_products'],
        complete_actual_tuple_degree_checks=len(degrees),
        receipt=str(receipt.relative_to(ROOT))), indent=2))


if __name__ == '__main__':
    main()

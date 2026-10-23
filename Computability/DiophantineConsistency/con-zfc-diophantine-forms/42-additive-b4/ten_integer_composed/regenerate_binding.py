#!/usr/bin/env python3
"""Bind the B4 parent to the complete nonzero683195 native tuple.

This is finite coefficient materialization only. It neither tests halting
nor imports the sibling builders. Run the backend builder first if its
payloads are absent. The arithmetic parent and all coefficient recipes
are copied from the delivered base ten-integer construction verbatim.
"""
from pathlib import Path
import gzip
import hashlib
import io
import json
from math import factorial

ROOT = Path(__file__).resolve().parent
BASE = ROOT.parent / 'ten_integer'
BACKEND = ROOT.parent / 'coefficient_backend'
PARENT_SHA256 = '1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287'
PORTS = ('beta', 'K', 'MC', 'MF_source')


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def write_json(path, body):
    path.write_text(json.dumps(body, indent=2) + '\n')


def compressed_integer(value):
    raw = value.to_bytes((value.bit_length() + 7) // 8, 'little')
    stream = io.BytesIO()
    with gzip.GzipFile(filename='', mode='wb', fileobj=stream,
                       compresslevel=9, mtime=0) as out:
        out.write(raw)
    return raw, stream.getvalue()


def main():
    data = ROOT / 'data'
    data.mkdir(exist_ok=True)
    parent_raw = (BASE / 'data/parent_quartic31.json').read_bytes()
    assert sha(parent_raw) == PARENT_SHA256
    (data / 'parent_quartic31.json').write_bytes(parent_raw)
    constants_raw = (BASE / 'data/constants.json').read_bytes()
    constants = json.loads(constants_raw)
    assert constants['parent_sha256'] == PARENT_SHA256
    assert constants['nu'] == 31 and len(constants['coefficient_records']) == 402
    assert constants['fixed_port_order'] == ['beta', 'K0', 'MC', 'MF']
    (data / 'constants.json').write_bytes(constants_raw)
    code_raw = (BASE / 'bose_chowla32.json').read_bytes()
    code = json.loads(code_raw)
    assert code['max_weight'] == 942302
    (ROOT / 'bose_chowla32.json').write_bytes(code_raw)

    backend_raw = (BACKEND / 'COEFFICIENT_BINDING.json').read_bytes()
    backend = json.loads(backend_raw)
    assert backend['d'] == 683195
    files, bits = [], []
    for name, source in zip(PORTS, backend['materialization']['files']):
        assert source['port'] == name
        packed = (BACKEND / source['file']).read_bytes()
        raw = gzip.decompress(packed)
        assert sha(raw) == source['sha256']
        assert sha(packed) == source['gzip_sha256']
        assert raw == (BACKEND / 'coefficients' / (name + '.bin')).read_bytes()
        bit_length = int.from_bytes(raw, 'little').bit_length()
        assert bit_length == source['bits']
        assert len(raw) == source['raw_bytes']
        (data / (name + '.bin.gz')).write_bytes(packed)
        bits.append(bit_length)
        files.append({'name': name, 'bit_length': bit_length,
                      'sha256': sha(raw), 'gzip_sha256': sha(packed),
                      'bytes': len(raw)})
    assert bits == [683195, 688546, 683195, 683196]
    binding = {
        'variant': backend['instance'],
        'source_commit': backend['source_commit'],
        'files': files,
        'complete_interface_proof': '../../coefficient_backend/PROOF.md',
        'backend_binding': '../../coefficient_backend/COEFFICIENT_BINDING.json',
        'backend_binding_sha256': sha(backend_raw),
        'warning': 'All four ports are from one complete new tuple. MF_source is already shifted.'}
    write_json(data / 'coefficients_binding.json', binding)

    records = []
    for row in constants['coefficient_records']:
        upper = sum(abs(term['coefficient']) <<
                    sum(power * bit for power, bit in zip(term['powers'], bits))
                    for term in row['coefficient_polynomial_in_fixed_ports'])
        # A_j < 2^bits[j], so this explicit triangle bound exceeds |c|.
        exponent = (upper + 1).bit_length()
        assert upper + 1 < (1 << exponent)
        records.append({'name': row['name'],
                        'strict_power_of_two_bound': exponent})
    index_exponent = max(row['strict_power_of_two_bound'] for row in records)
    assert index_exponent == 2743487
    margin_exponent = (2 * factorial(4) * 33**4).bit_length()
    assert margin_exponent == 26
    # The source bound requires a strict inequality; reserve 27 bits as
    # in the base construction, and round upward to an even exponent.
    beta_exponent = index_exponent + 27
    beta_exponent += beta_exponent % 2
    assert beta_exponent == 2743514
    assert 2 * factorial(4) * 33**4 < 1 << (beta_exponent - index_exponent)
    write_json(data / 'index_bound.json', {
        'status': 'PASS', 'index_exponent': index_exponent,
        'port_bit_lengths': bits, 'records': records,
        'recipe': 'For every coefficient: upper=sum |a_e|*2^(sum e_j bits_j); |c|+1<=upper+1<2^record_bound.',
        'beta_sun_exponent': beta_exponent,
        'source_coefficient_count': len(records)})
    beta_raw, beta_gzip = compressed_integer(1 << beta_exponent)
    (data / 'beta_sun.bin.gz').write_bytes(beta_gzip)
    beta_record = {
        'formula': f'2^{beta_exponent}', 'power_of_two_exponent': beta_exponent,
        'bit_length': beta_exponent + 1, 'raw_byte_length': len(beta_raw),
        'sha256': sha(beta_raw), 'gzip_sha256': sha(beta_gzip),
        'encoding': 'Unsigned little-endian integer, gzip compressed',
        'file': 'beta_sun.bin.gz'}
    instance = {
        'instance': 'b4-signed10-structural-quintic-nonzero683195',
        'domain': 'Ten unrestricted integers',
        'variables': ['f', 'g', 'h', 'k', 'l', 'w', 'x', 'y', 'z', 'm'],
        'parent': 'parent_quartic31.json', 'parent_sha256': PARENT_SHA256,
        'weighted_coefficients': 'constants.json',
        'coefficient_bound': 'index_bound.json',
        'fixed_port_order': ['beta', 'K0', 'MC', 'MF'],
        'four_ports': {'beta': 'beta.bin.gz', 'K0': 'K.bin.gz',
                       'MC': 'MC.bin.gz', 'MF': 'MF_source.bin.gz'},
        'four_port_binding': 'coefficients_binding.json',
        'beta_sun': beta_record,
        'nu': 31, 'delta': 4, 'dummy_input': 0,
        't': code['max_weight'], 'Lcode': 4 * code['max_weight'],
        'unknown_parameters': [],
        'source_polynomial': 'P0(n)=sum of 22 positive-parent residuals after n_i+1 shift; 31 natural unknowns and no input digit',
        'primary_equation': '../generated/b4_signed10.json',
        'proof': '../PROOF.md',
        'ordinary_mathematical_proof': True,
        'end_to_end_machine_checked_certificate': False,
        'coding': 'Bose-Chowla B4; 31 witness digit positions from ../bose_chowla32.json',
        'active_binding_notice': 'This file and coefficients_binding.json override historical tuple metadata inside the byte-preserved parent JSON.',
        'transport_convention': 'Parent z is old z_old; retained59 z_new=z_old-1. The outer ten-integer z is a separate variable.',
        'parent_auxiliary_y': 'Unchanged from retained59; only the all-coordinate positive-to-natural shift is applied.'}
    write_json(data / 'INSTANCE.json', instance)
    composition = {
        'status': 'PASS',
        'instance': instance['instance'],
        'parent_sha256': PARENT_SHA256,
        'symbolic_constants_sha256': sha(constants_raw),
        'b4_code_sha256': sha(code_raw),
        'backend_binding_sha256': sha(backend_raw),
        'ports': files,
        'weighted_coefficient_bound_exponent': index_exponent,
        'beta_sun': beta_record,
        'four_native_ports_raw_bytes': sum(row['bytes'] for row in files),
        'five_fixed_payloads_raw_bytes': sum(row['bytes'] for row in files) + len(beta_raw),
        'new_unknown_parameters': [],
        'source': 'Sibling ten_integer literal parent/recipes and coefficient_backend complete coherent tuple.',
        'proof_boundary': 'Finite rebinding checks supplement PROOF.md and the inherited universal compiler/Pell/Sun theorems.'}
    write_json(ROOT / 'COMPOSITION_BINDING.json', composition)
    print(json.dumps(composition, indent=2))


if __name__ == '__main__':
    main()

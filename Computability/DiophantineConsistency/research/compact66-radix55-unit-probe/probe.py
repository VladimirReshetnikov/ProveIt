#!/usr/bin/env python3
"""Held three-prime modular probe; no new radix55 tuple is constructed."""
import sys

sys.dont_write_bytecode = True

import argparse
from copy import deepcopy
import gzip
from hashlib import sha256
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REPO = ROOT.parents[1]
INDEXED = ROOT / 'research/indexed-tile-enumeration'
COMPACT = ROOT / 'candidates/one-page-compact66'
TEMPLATE = 'research/compact66-radix65-unit-probe'
MODULI = (5, 8807, 581197)
PAYLOADS = {'probe.py', 'README.md', 'PROOF.md', 'TOOLCHAIN.md', 'SOURCE_PINS.json'}
PARENTS = {'candidates/one-page-compact66', 'research/indexed-tile-enumeration',
           'research/compact66-radix-boundary', 'research/compact66-radix65-unit-probe-verification',
           'research/compact66-radix65-native-adapter', 'research/compact66-radix55-bootstrap'}
STEM = '/tmp/compact66-radix55-unit-probe-'
OUTPUTS = {False: (STEM + 'normal.json', STEM + 'root-normal.json'),
           True: (STEM + 'optimized.json', STEM + 'root-optimized.json')}


def need(ok, reason):
    if not ok:
        raise ValueError(reason)


def digest(blob):
    return sha256(blob).hexdigest()


def encode(value):
    return (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, 'no duplicate JSON keys')
        result[key] = value
    return result


def reject_constant(text):
    raise ValueError('no nonfinite JSON constant: ' + text)


def load(path):
    return json.loads(path.read_bytes(), object_pairs_hook=unique_object, parse_constant=reject_constant)


def ordinary_path(base, name):
    need(type(name) is str and name and not Path(name).is_absolute()
         and all(p not in ('', '.', '..') for p in name.split('/')), 'safe relative input path')
    path = base
    for component in name.split('/'):
        path = path / component
        need(not path.is_symlink(), 'no input symlink: ' + name)
    need(path.is_file() and path.resolve().is_relative_to(base.resolve()), 'regular contained input: ' + name)
    return path


def file_record(path):
    blob = path.read_bytes()
    return {'sha256': digest(blob), 'bytes': len(blob)}


def checked_record(record):
    need(type(record) is dict and set(record) == {'sha256', 'bytes'}
         and type(record['bytes']) is int and record['bytes'] >= 0
         and type(record['sha256']) is str and len(record['sha256']) == 64
         and all(c in '0123456789abcdef' for c in record['sha256']), 'strict byte/hash record')
    return record


def authenticate_hold(folder, schema):
    held = load(ordinary_path(folder, 'HOLD_INVENTORY.json'))
    need(type(held) is dict and set(held) == {'schema', 'scope', 'files', 'payload_files', 'payload_bytes'}
         and held['schema'] == schema and type(held['scope']) is str
         and type(held['files']) is dict and set(held['files']) == PAYLOADS
         and type(held['payload_files']) is int and held['payload_files'] == len(PAYLOADS)
         and type(held['payload_bytes']) is int, 'exact held payload schema/policy')
    need(not any(p.is_symlink() for p in folder.rglob('*')), 'no held-tree symlink')
    actual = {p.relative_to(folder).as_posix() for p in folder.rglob('*')
              if p.is_file() and p != folder / 'HOLD_INVENTORY.json'}
    need(actual == PAYLOADS, 'closed held inventory')
    for name, record in held['files'].items():
        need(file_record(ordinary_path(folder, name)) == checked_record(record), 'held whole payload: ' + name)
    need(sum(record['bytes'] for record in held['files'].values()) == held['payload_bytes'], 'held byte census')
    return held


def authenticate():
    authenticate_hold(HERE, 'compact66_radix55_probe_hold_v1')
    pins = load(ordinary_path(HERE, 'SOURCE_PINS.json'))
    need(type(pins) is dict and set(pins) == {'schema', 'path_base', 'scope', 'files', 'own_core',
         'closed_parents', 'held_template', 'candidate'} and pins['schema'] == 'compact66_radix55_probe_pins_v1'
         and pins['path_base'] == 'Computability/DiophantineConsistency' and type(pins['scope']) is str,
         'strict source pin schema/base')
    candidate = pins['candidate']
    need(type(candidate) is dict and set(candidate) == {'radix_bits', 'fixed_moduli',
         'unit_values_unknown_during_preparation', 'unit_nonzero_not_verification_gate'}
         and type(candidate['radix_bits']) is int and candidate['radix_bits'] == 55
         and type(candidate['fixed_moduli']) is list and all(type(p) is int for p in candidate['fixed_moduli'])
         and candidate['fixed_moduli'] == list(MODULI)
         and candidate['unit_values_unknown_during_preparation'] is True
         and candidate['unit_nonzero_not_verification_gate'] is True, 'exact unknown three-unit question')
    need(type(pins['own_core']) is dict and set(pins['own_core']) == PAYLOADS - {'SOURCE_PINS.json'},
         'complete own code/prose pin set')
    for name, record in pins['own_core'].items():
        need(file_record(ordinary_path(HERE, name)) == checked_record(record), 'own core: ' + name)
    need(type(pins['files']) is dict, 'external file mapping')
    for name, record in pins['files'].items():
        need(file_record(ordinary_path(ROOT, name)) == checked_record(record), 'whole external: ' + name)
    need(type(pins['closed_parents']) is dict and set(pins['closed_parents']) == PARENTS, 'exact six parents')
    parent_records = {}
    for relative, expected in pins['closed_parents'].items():
        parent = ROOT / relative
        manifest_path = ordinary_path(ROOT, relative + '/MANIFEST.json')
        need(file_record(manifest_path) == checked_record(expected), 'parent manifest: ' + relative)
        need(not any(p.is_symlink() for p in parent.rglob('*')), 'no parent-tree symlink')
        manifest = load(manifest_path)
        need(type(manifest) is dict and type(manifest.get('files')) is dict, 'parent member mapping')
        members = manifest['files']
        actual = {p.relative_to(parent).as_posix() for p in parent.rglob('*')
                  if p.is_file() and p != manifest_path}
        need(actual == set(members), 'whole parent member set: ' + relative)
        total = 0
        for name, entry in members.items():
            record = file_record(ordinary_path(parent, name))
            if type(entry) is dict:
                need(record == checked_record(entry), 'typed parent member: ' + relative + '/' + name)
            else:
                need(type(entry) is str and record['sha256'] == entry, 'hash parent member: ' + relative + '/' + name)
            need(pins['files'].get(relative + '/' + name) == record, 'flattened parent member pin')
            total += record['bytes']
        parent_records[relative] = {'manifest': expected, 'payloads': len(members), 'payload_bytes': total}
    template = pins['held_template']
    need(type(template) is dict and set(template) == {'folder', 'inventory'} and template['folder'] == TEMPLATE,
         'exact readonly template identity')
    template_folder = ROOT / TEMPLATE
    authenticate_hold(template_folder, 'compact66_radix65_probe_hold_v1')
    need(file_record(ordinary_path(ROOT, TEMPLATE + '/HOLD_INVENTORY.json')) == checked_record(template['inventory']),
         'whole readonly template inventory')
    for name in PAYLOADS | {'HOLD_INVENTORY.json'}:
        need(pins['files'].get(TEMPLATE + '/' + name) == file_record(ordinary_path(template_folder, name)),
             'flattened readonly template member')
    return {'hold_sha256': digest((HERE / 'HOLD_INVENTORY.json').read_bytes()),
            'source_pins_sha256': digest((HERE / 'SOURCE_PINS.json').read_bytes()),
            'held_payloads': len(PAYLOADS), 'external_files': len(pins['files']),
            'own_core_files': len(pins['own_core']), 'closed_parents': parent_records,
            'readonly_template_inventory': template['inventory']}


def receipt_path(text):
    need(text in OUTPUTS[bool(sys.flags.optimize)], 'fixed same-mode first/fresh receipt path')
    path = Path(text)
    need(path.is_absolute() and '..' not in path.parts and path.parent == Path('/tmp'), 'external receipt location')
    for parent in reversed(path.parents):
        need(not parent.is_symlink(), 'no receipt parent symlink')
    need(not path.is_symlink() and not path.exists(), 'receipt path must be absent')
    need(not path.resolve().is_relative_to(REPO), 'receipt outside whole repository')
    return path


def complete_existing_ports():
    current = load(COMPACT / 'COEFFICIENT_BINDING.json')
    original = load(INDEXED / 'coefficients/BINDING.json')
    need(type(current) is dict and type(original) is dict and type(current.get('ports')) is dict
         and current['ports'] == original.get('ports')
         and set(current['ports']) == {'beta', 'K0', 'MC', 'MF'}, 'whole coherent existing four-port association')
    expected_files = {'beta': 'beta.bin.gz', 'K0': 'K.bin.gz', 'MC': 'MC.bin.gz', 'MF': 'MF_source.bin.gz'}
    records = {}
    k_raw = None
    total = 0
    for port in ('beta', 'K0', 'MC', 'MF'):
        entry = current['ports'][port]
        need(type(entry) is dict and set(entry) == {'file', 'bits', 'gzip_sha256', 'raw_sha256'}
             and entry['file'] == expected_files[port] and type(entry['bits']) is int and entry['bits'] > 0,
             'exact port record/name: ' + port)
        blob = (COMPACT / 'coefficients' / entry['file']).read_bytes()
        need(blob == (INDEXED / 'coefficients' / entry['file']).read_bytes(), 'entire parent gzip equality: ' + port)
        raw = gzip.decompress(blob)
        need(raw and raw[-1] != 0, 'minimal existing unsigned little-endian bytes: ' + port)
        bits = 8 * (len(raw) - 1) + raw[-1].bit_length()
        need(bits == entry['bits'] and digest(blob) == entry['gzip_sha256']
             and digest(raw) == entry['raw_sha256'], 'whole compressed/raw port metadata: ' + port)
        records[port] = {**entry, 'raw_bytes': len(raw)}
        total += len(raw)
        if port == 'K0':
            k_raw = raw
    need(type(current.get('raw_bytes')) is int and total == current['raw_bytes'] == 295388,
         'complete old tuple byte total')
    return records, k_raw


def control_terms():
    first = [(1023 + j, 1 << (10 + j)) for j in range(8)] + [(1003 + j, 1 << (27 + j)) for j in range(8)]
    second = [(1013 + j, 1 << (18 + j)) for j in range(9)] + [(983 + j, 1 << (35 + j)) for j in range(9)]
    third = [(1031, 1 << 44), (1022, 1 << 45), (1011, 1 << 46), (992, 1 << 47)]
    fourth = [(1095, 1 << 48), (2195, 1 << 49), (3296, 1 << 50)]
    return first + second + third + fourth


def phi_from_tiles(tiles, controls):
    need(type(tiles) is list and len(tiles) == 943, 'exact ordered 943-tile list')
    phi = [0] * 3297
    for i, tile in enumerate(tiles):
        need(type(tile) is list and len(tile) == 4 and all(type(v) is int for v in tile), 'integer four-coordinate tile')
        w, n, e, s = tile
        need(0 <= w < 256 and 0 <= n < 512 and 0 <= e < 256 and 0 <= s < 512, 'every tile field bound')
        phi[i] = 1 + (1 << 10) * ((1 << 34) - w - (n << 8) - (e << 17) - (s << 25))
        need(0 < phi[i] < 1 << 45, 'selector coefficient bound')
    for position, value in controls:
        need(type(position) is int and type(value) is int and 943 <= position <= 3296 and value > 0,
             'positive integer control contribution')
        phi[position] += value
    need(phi[1063] == phi[1064] == 0, 'both zero dummy holes')
    support = set(range(943)) | set(range(983, 993)) | set(range(1003, 1012)) | set(range(1013, 1032))
    support |= {1095, 2195, 3296}
    need({i for i, c in enumerate(phi) if c} == support and len(support) == 984, 'entire nonzero Phi support')
    need(all(0 <= c < 1 << 67 for c in phi), 'old-radix digit bounds')
    return phi


def phi_from_existing_k(raw):
    need(type(raw) is bytes and raw and raw[-1] != 0, 'minimal K little-endian encoding')
    k = int.from_bytes(raw, 'little')  # Only the existing accepted67-bit K is parsed.
    need(k.bit_length() == 592884 and len(raw) == (k.bit_length() + 7) // 8, 'existing K size/byte order')
    base = sum(1 << (67 * e) for e in (30, 62, 1100, 2201, 8849))
    rest = k - base
    need(rest > 0, 'positive existing K non-base part')
    quotient, remainder = divmod(rest, 1 << (67 * 1097))
    need(remainder == 0, 'existing K first exact factor')
    reversed_value, remainder = divmod(quotient, 1 + (1 << (67 * 1102)))
    need(remainder == 0, 'existing K second exact factor')
    digits = []
    for _ in range(3297):
        digits.append(reversed_value & ((1 << 67) - 1))
        reversed_value >>= 67
    need(reversed_value == 0, 'complete existing K reversed polynomial degree')
    return list(reversed(digits))


def modular_routes(left, right):
    results = []
    for prime in MODULI:
        rho = pow(2, 55, prime)
        inverse = pow(rho, -1, prime)
        b = pow(rho, 8807, prime)
        phi_inverse = 0
        power = 1
        for coefficient in left:
            phi_inverse = (phi_inverse + coefficient * power) % prime
            power = power * inverse % prime
        k_left = (sum(pow(rho, e, prime) for e in (30, 62, 1100, 2201, 8849))
                  + (pow(rho, 4393, prime) + pow(rho, 5495, prime)) * phi_inverse) % prime
        h_left = (1 + b * k_left + b * b) % prime
        reversed_horner = 0
        for coefficient in right:
            reversed_horner = (reversed_horner * rho + coefficient) % prime
        dc_right = (sum(pow(rho, e, prime) for e in (30, 62, 1100, 2201))
                    + pow(rho, 1097, prime) * (1 + pow(rho, 1102, prime)) * reversed_horner) % prime
        dr = pow(rho, 42, prime)
        k_right = (dc_right + b * dr) % prime
        h_right = (1 + b * dc_right + b * b * (dr + 1)) % prime
        need(k_left == k_right and h_left == h_right, 'two complete modular evaluation routes')
        results.append({'prime': prime, 'rho_mod': rho, 'B_mod': b, 'K_mod_inverse_route': k_left,
                        'K_mod_positive_route': k_right, 'H0_inverse_route': h_left,
                        'H0_positive_route': h_right, 'unit': h_left != 0})
    return results


def verify_model(model, evaluate=True):
    left = phi_from_tiles(model['tiles'], model['controls'])
    right = phi_from_existing_k(model['k_raw'])
    need(left == right, 'all 3297 Phi coefficients and ordered selector bindings')
    need(len({tuple(tile) for tile in model['tiles']}) == 943, 'all 943 distinct tiles')
    need(model['tiles'][0] == [2, 435, 3, 1] and model['tiles'][1] == [5, 0, 0, 0]
         and model['tiles'][929] == [3, 436, 4, 4], 'Start/Forbidden/literal initializer association')
    return left, modular_routes(left, right) if evaluate else None


def artifact_controls(original):
    before = deepcopy(original)
    cases = []
    changed = deepcopy(original); changed['tiles'][2][0] ^= 1
    cases.append(('ordered_tile_coordinate', changed, 'all 3297 Phi coefficients'))
    changed = deepcopy(original); changed['tiles'][2], changed['tiles'][3] = changed['tiles'][3], changed['tiles'][2]
    cases.append(('ordered_tile_swap', changed, 'all 3297 Phi coefficients'))
    changed = deepcopy(original); changed['tiles'][2][0] = True
    cases.append(('boolean_tile_label', changed, 'integer four-coordinate tile'))
    changed = deepcopy(original); changed['controls'].append((1063, 1))
    cases.append(('nonzero_dummy', changed, 'both zero dummy holes'))
    changed = deepcopy(original); position, value = changed['controls'][0]; changed['controls'][0] = (position, value + 1)
    cases.append(('actual_control_coefficient', changed, 'all 3297 Phi coefficients'))
    changed = deepcopy(original); changed['k_raw'] = bytes([changed['k_raw'][0] ^ 1]) + changed['k_raw'][1:]
    cases.append(('existing_k_low_bit', changed, 'existing K first exact factor'))
    changed = deepcopy(original); changed['k_raw'] += b'\0'
    cases.append(('nonminimal_existing_k_bytes', changed, 'minimal K little-endian encoding'))
    rejected = []
    for name, changed, expected in cases:
        try:
            verify_model(changed, evaluate=False)
        except ValueError as error:
            need(expected in str(error), 'intended semantic rejection: ' + name)
            rejected.append({'name': name, 'reason': str(error)})
        else:
            raise ValueError('accepted actual-artifact corruption: ' + name)
    positive = []
    changed = deepcopy(original); changed['controls'].reverse()
    verify_model(changed, evaluate=False); positive.append('control_contribution_order')
    changed = deepcopy(original); position, value = changed['controls'][0]
    changed['controls'][0] = (position, value - 1); changed['controls'].append((position, 1))
    verify_model(changed, evaluate=False); positive.append('exact_control_coefficient_split')
    need(original == before, 'controls do not mutate source model')
    return {'rejected': rejected, 'negative_count': len(rejected), 'valid': positive, 'valid_count': len(positive)}


def main():
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    provenance = authenticate()
    output = receipt_path(args.output)
    ports, raw = complete_existing_ports()
    model = {'tiles': load(INDEXED / 'TILES.json'), 'controls': control_terms(), 'k_raw': raw}
    need(len(model['controls']) == 41, 'four literal control groups contain 41 terms')
    phi, residues = verify_model(model)
    controls = artifact_controls(model)
    all_units = all(row['unit'] for row in residues)
    report = {'schema': 'compact66_radix55_modular_unit_probe_v1', 'status': 'PASS',
              'optimized_python': bool(sys.flags.optimize), 'provenance': provenance,
              'existing_coherent_ports': ports, 'existing_raw_port_bytes': 295388,
              'phi': {'coefficients': len(phi), 'ordered_tiles': 943, 'literal_control_terms': 41,
                      'nonzero_coefficients': sum(c != 0 for c in phi), 'support_with_dummy_holes': 986,
                      'zero_dummy_indices': [1063, 1064], 'canonical_array_sha256': digest(encode(phi)),
                      'all_coefficients_equal_by_two_routes': True},
              'candidate_radix_bits': 55, 'fixed_moduli': list(MODULI), 'modular_results': residues,
              'candidate_units_nonzero': all_units, 'all_three_unit_conditions_nonzero': all_units,
              'scientific_outcome': 'all_three_units_nonzero' if all_units else 'controller_unit_obstruction',
              'scientific_outcome_is_not_a_verification_gate': True, 'controls': controls,
              'new_radix55_tuple_or_native_or_endpoint_claim': False,
              'retained_scope': 'Accepted ordinary native/source contracts only; no fresh transitive/native/Lean audit.'}
    need(authenticate() == provenance, 'all held/external input bytes unchanged after verification')
    receipt_path(args.output)
    blob = encode(report)
    with output.open('xb') as stream:
        stream.write(blob)
    sys.stdout.write(blob.decode())


if __name__ == '__main__':
    main()

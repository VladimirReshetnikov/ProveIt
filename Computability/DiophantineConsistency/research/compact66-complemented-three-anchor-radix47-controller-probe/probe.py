#!/usr/bin/env python3
"""CODE ONLY/HOLD: bounded complemented-positive-color three-anchor47 controller probe."""
import sys

sys.dont_write_bytecode = True

import argparse
from copy import deepcopy
import gzip
from hashlib import sha256
import json
from math import gcd, isqrt
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REPO = ROOT.parents[1]
COMPACT = ROOT / 'candidates/one-page-compact66'
INDEXED = ROOT / 'research/indexed-tile-enumeration'
PREFIX = 'Computability/DiophantineConsistency/'
TEMPLATE = 'research/compact66-shared-marker-radix49-certificate-probe'
PARENTS = {'candidates/one-page-compact66', 'research/indexed-tile-enumeration',
           'research/compact66-shared-marker-radix49', 'research/compact66-radix51-local-resets',
           'research/compact66-radix53-carry-tolerance', 'research/compact66-radix53-page-verification',
           'research/compact66-complemented-three-anchor-radix47', 'research/compact66-three-anchor-radix49',
           'research/compact66-three-anchor-radix47',
           'research/compact66-shared-marker-radix49-certificate-probe-verification'}
PAYLOADS = {'probe.py', 'README.md', 'PROOF.md', 'TOOLCHAIN.md', 'SOURCE_PINS.json'}
BITS, CELL, D, STEP, FIRST_M, LAST_M = 47, 8807, 47 * 8807, 101269, 5, 205
ANCHORS = (1095, 2195, 3296)
REMOVED = (992, 1011, 1022, 1031)
COMPLEMENT = (255, 511, 255, 511)
FIXED = (47, 8807)
STEM = '/tmp/compact66-complemented-three-anchor-radix47-controller-probe-'
OUTPUTS = {False: (STEM + 'normal.json', STEM + 'root-normal.json'),
           True: (STEM + 'optimized.json', STEM + 'root-optimized.json')}
CAPTURES = [STEM + role + suffix for role in ('normal', 'optimized', 'root-normal', 'root-optimized')
            for suffix in ('.json', '.stdout', '.stderr')]
QUESTION = {'radix_bits': 47, 'cell_digits': 8807, 'd': 47 * 8807,
            'candidate_step': 101269, 'first_m': 5, 'last_m': 205,
            'fixed_unit_primes': [47, 8807], 'full_stride_prime_moduli': [47, 8807],
            'coefficient_profile': 'complemented-three-anchor47-low26',
            'positive_color_complement_maxima': list(COMPLEMENT), 'selector_spacing_bits': 10,
            'anchor_positions': list(ANCHORS), 'common_anchor_weight': '2^44',
            'removed_occupancy_positions': list(REMOVED),
            'all_unit_values_unknown_in_preparation': True,
            'synthetic_control_fixture': 'abstract prime5, exponent1, B2, K1; never an actual47 lambda',
            'scientific_obstruction_or_exhaustion_is_not_verification_failure': True}


def need(value, reason):
    if not value:
        raise ValueError(reason)


def digest(raw):
    return sha256(raw).hexdigest()


def encode(value):
    return (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()


def unique_object(items):
    result = {}
    for key, value in items:
        need(key not in result, 'duplicate JSON key: ' + key)
        result[key] = value
    return result


def reject_constant(value):
    raise ValueError('nonfinite JSON constant: ' + value)


def load(path):
    return json.loads(path.read_bytes(), object_pairs_hook=unique_object, parse_constant=reject_constant)


def ordinary_path(base, name):
    need(type(name) is str and name and not Path(name).is_absolute()
         and all(p not in ('', '.', '..') for p in name.split('/')), 'safe relative path')
    path = base
    for part in name.split('/'):
        path = path / part
        need(not path.is_symlink(), 'no input symlink: ' + name)
    need(path.is_file() and path.resolve().is_relative_to(base.resolve()), 'regular contained file: ' + name)
    return path


def record(path):
    raw = path.read_bytes()
    return {'bytes': len(raw), 'sha256': digest(raw)}


def checked_record(value):
    need(type(value) is dict and set(value) == {'bytes', 'sha256'}
         and type(value['bytes']) is int and value['bytes'] >= 0
         and type(value['sha256']) is str and len(value['sha256']) == 64
         and all(c in '0123456789abcdef' for c in value['sha256']), 'strict byte/hash record')
    return value


def typed_equal(left, right):
    if type(left) is not type(right):
        return False
    if type(left) is dict:
        return set(left) == set(right) and all(typed_equal(left[k], right[k]) for k in left)
    if type(left) is list:
        return len(left) == len(right) and all(typed_equal(a, b) for a, b in zip(left, right))
    return left == right


def whole_inventory(folder, filename, expected_names=None):
    manifest = load(ordinary_path(folder, filename))
    need(type(manifest) is dict and type(manifest.get('files')) is dict, 'inventory member mapping')
    entries = manifest['files']
    need(not any(p.is_symlink() for p in folder.rglob('*')), 'no inventory-tree symlinks')
    actual = {p.relative_to(folder).as_posix() for p in folder.rglob('*') if p.is_file()}
    need(actual == set(entries) | {filename}, 'complete inventory membership: ' + str(folder))
    if expected_names is not None:
        need(set(entries) == expected_names, 'exact held payload names')
    records = {}
    for name, entry in entries.items():
        value = record(ordinary_path(folder, name))
        if type(entry) is dict:
            need(value == checked_record(entry), 'inventory whole member: ' + name)
        else:
            need(type(entry) is str and value['sha256'] == entry, 'historical hash-only member: ' + name)
        records[name] = value
    return manifest, records


def authenticate():
    held, members = whole_inventory(HERE, 'HOLD_INVENTORY.json', PAYLOADS)
    need(set(held) == {'schema', 'scope', 'payload_files', 'payload_bytes', 'files'}
         and held['schema'] == 'complemented_three_anchor47_controller_probe_hold_v1' and type(held['scope']) is str
         and type(held['payload_files']) is int and held['payload_files'] == 5
         and type(held['payload_bytes']) is int
         and held['payload_bytes'] == sum(x['bytes'] for x in members.values()), 'strict held schema/census')
    pins = load(ordinary_path(HERE, 'SOURCE_PINS.json'))
    need(type(pins) is dict and set(pins) == {'schema', 'path_base', 'scope', 'question', 'files',
         'own_core', 'closed_parents', 'readonly_template', 'python', 'future_capture_paths'}
         and pins['schema'] == 'complemented_three_anchor47_controller_probe_pins_v1'
         and pins['path_base'] == 'Proofs repository root'
         and type(pins['scope']) is str and typed_equal(pins['question'], QUESTION), 'strict pin question/schema')
    need(typed_equal(pins['future_capture_paths'], CAPTURES), 'exact twelve first/fresh capture paths')
    need(type(pins['own_core']) is dict and set(pins['own_core']) == PAYLOADS - {'SOURCE_PINS.json'},
         'complete own code/prose pins')
    for name, expected in pins['own_core'].items():
        need(record(ordinary_path(HERE, name)) == checked_record(expected), 'own core: ' + name)
    need(type(pins['files']) is dict, 'flat external pin mapping')
    for name, expected in pins['files'].items():
        need(record(ordinary_path(REPO, name)) == checked_record(expected), 'external whole file: ' + name)
    need(type(pins['closed_parents']) is dict and set(pins['closed_parents']) == PARENTS, 'exact ten protected parents')
    parents = {}
    for relative, expected in pins['closed_parents'].items():
        folder = ROOT / relative
        need(record(ordinary_path(ROOT, relative + '/MANIFEST.json')) == checked_record(expected), 'parent seal')
        _, files = whole_inventory(folder, 'MANIFEST.json')
        for name, value in files.items():
            need(pins['files'].get(PREFIX + relative + '/' + name) == value, 'every parent payload flattened')
        need(pins['files'].get(PREFIX + relative + '/MANIFEST.json') == expected, 'parent manifest flattened')
        parents[relative] = {'manifest': expected, 'payloads': len(files),
                             'payload_bytes': sum(v['bytes'] for v in files.values())}
    template = pins['readonly_template']
    need(type(template) is dict and set(template) == {'folder', 'inventory'}
         and template['folder'] == TEMPLATE, 'exact read-only template policy')
    need(record(ordinary_path(ROOT, TEMPLATE + '/HOLD_INVENTORY.json'))
         == checked_record(template['inventory']), 'template inventory')
    _, files = whole_inventory(ROOT / TEMPLATE, 'HOLD_INVENTORY.json', PAYLOADS)
    for name, value in files.items():
        need(pins['files'].get(PREFIX + TEMPLATE + '/' + name) == value, 'template payload flattened')
    need(pins['files'].get(PREFIX + TEMPLATE + '/HOLD_INVENTORY.json') == template['inventory'], 'template seal flattened')
    python = pins['python']
    need(type(python) is dict and set(python) == {'resolved_path', 'record'}
         and type(python['resolved_path']) is str
         and str(Path(sys.executable).resolve()) == python['resolved_path'], 'reviewed Python resolution')
    need(record(Path(python['resolved_path'])) == checked_record(python['record']), 'reviewed Python bytes')
    return {'hold': record(HERE / 'HOLD_INVENTORY.json'), 'pins': record(HERE / 'SOURCE_PINS.json'),
            'external_files': len(pins['files']), 'own_core_files': len(pins['own_core']),
            'parents': parents, 'readonly_template': template, 'python': python}


def receipt_path(text):
    need(text in OUTPUTS[bool(sys.flags.optimize)], 'fixed same-mode first/fresh output')
    path = Path(text)
    need(path.parent == Path('/tmp') and not path.is_symlink() and not path.exists(), 'absent external receipt')
    need(not any(p.is_symlink() for p in path.parents) and not path.resolve().is_relative_to(REPO),
         'receipt outside whole repository without symlinks')
    return path


def existing_ports():
    a = load(COMPACT / 'COEFFICIENT_BINDING.json')
    b = load(INDEXED / 'coefficients/BINDING.json')
    need(typed_equal(a['ports'], b['ports']) and set(a['ports']) == {'beta', 'K0', 'MC', 'MF'},
         'complete old coherent four-port association')
    filenames = {'beta': 'beta.bin.gz', 'K0': 'K.bin.gz', 'MC': 'MC.bin.gz', 'MF': 'MF_source.bin.gz'}
    result, total, k_raw = {}, 0, None
    for port, filename in filenames.items():
        entry = a['ports'][port]
        need(type(entry) is dict and set(entry) == {'file', 'bits', 'gzip_sha256', 'raw_sha256'}
             and entry['file'] == filename and type(entry['bits']) is int and entry['bits'] > 0,
             'strict old port schema: ' + port)
        raw_gzip = ordinary_path(COMPACT, 'coefficients/' + filename).read_bytes()
        need(raw_gzip == ordinary_path(INDEXED, 'coefficients/' + filename).read_bytes(), 'old gzip association')
        raw = gzip.decompress(raw_gzip)
        need(raw and raw[-1] != 0, 'minimal old little-endian bytes')
        need(8 * (len(raw) - 1) + raw[-1].bit_length() == entry['bits']
             and digest(raw_gzip) == entry['gzip_sha256'] and digest(raw) == entry['raw_sha256'], 'all old port bytes')
        result[port] = {**entry, 'raw_bytes': len(raw)}
        total += len(raw)
        if port == 'K0':
            k_raw = raw
    need(type(a['raw_bytes']) is int and total == a['raw_bytes'] == 295388, 'entire old tuple census')
    return result, k_raw


def new_controls():
    return ([[1023+j, 1 << (10+j)] for j in range(8)]
            + [[1003+j, 1 << (27+j)] for j in range(8)]
            + [[1013+j, 1 << (18+j)] for j in range(9)]
            + [[983+j, 1 << (35+j)] for j in range(9)]
            + [[e, 1 << 44] for e in ANCHORS])


def check_color_complement(old_tiles, positive_tiles):
    need(type(old_tiles) is list and len(old_tiles) == 943
         and type(positive_tiles) is list and len(positive_tiles) == 943,
         'two complete ordered tile lists')
    for old, new in zip(old_tiles, positive_tiles):
        need(type(old) is list and len(old) == 4 and all(type(v) is int for v in old),
             'integer old four-coordinate tile')
        need(type(new) is list and len(new) == 4 and all(type(v) is int for v in new),
             'integer positive four-coordinate tile')
        w, n, p, s = old
        need(0 <= w < 250 and 0 <= n < 439 and 0 <= p < 250 and 0 <= s < 439,
             'whole actual old color domains')
        need(new == [maximum - v for maximum, v in zip(COMPLEMENT, old)],
             'whole positive color complement')


def direct_phi(positive_tiles, controls):
    need(type(positive_tiles) is list and len(positive_tiles) == 943, 'exact ordered positive tile list')
    phi = [0] * 3297
    for i, tile in enumerate(positive_tiles):
        need(type(tile) is list and len(tile) == 4 and all(type(v) is int for v in tile),
             'integer positive four-coordinate tile')
        w, n, p, s = tile
        need(6 <= w <= 255 and 73 <= n <= 511 and 6 <= p <= 255 and 73 <= s <= 511,
             'positive complemented tile field bound')
        phi[i] = 1 + (1 << 44) - (w << 10) - (n << 18) - (p << 27) - (s << 35)
        need(0 < phi[i] < 1 << 44, 'complemented selector coefficient bound')
    need(type(controls) is list, 'control contribution list')
    for pair in controls:
        need(type(pair) is list and len(pair) == 2 and all(type(v) is int for v in pair),
             'strict control contribution pair')
        e, c = pair
        need(943 <= e <= 3296 and c > 0, 'control contribution range/positive coefficient')
        phi[e] += c
    need(phi[1063] == phi[1064] == 0, 'both zero dummy holes')
    support = (set(range(943)) | set(range(983, 992)) | set(range(1003, 1011))
               | set(range(1013, 1022)) | set(range(1023, 1031)) | set(ANCHORS))
    need({e for e, c in enumerate(phi) if c} == support and len(support) == 980, 'whole new Phi support')
    need(all(0 <= c < 1 << BITS for c in phi), 'new-radix coefficient digit bound')
    return phi


def recovered_phi(raw):
    need(type(raw) is bytes and raw and raw[-1] != 0, 'minimal K little-endian encoding')
    k = int.from_bytes(raw, 'little')
    need(k.bit_length() == 592884 and len(raw) == 74111, 'whole existing K size')
    tail = k - sum(1 << (67 * e) for e in (30, 62, 1100, 2201, 8849))
    need(tail > 0, 'positive old K tail')
    tail, remainder = divmod(tail, 1 << (67 * 1097))
    need(remainder == 0, 'existing K first exact factor')
    tail, remainder = divmod(tail, 1 + (1 << (67 * 1102)))
    need(remainder == 0, 'existing K second exact factor')
    reverse = []
    for _ in range(3297):
        reverse.append(tail & ((1 << 67) - 1))
        tail >>= 67
    need(tail == 0, 'whole old reversed polynomial')
    old = list(reversed(reverse))
    # This independent OLD family check precedes every marker replacement.
    label = {}
    for start, count, bit in [(1023, 8, 10), (1003, 8, 27), (1013, 9, 18), (983, 9, 35)]:
        for j in range(count):
            need(start+j not in label, 'disjoint old label positions')
            label[start+j] = 1 << (bit+j)
    legacy = {1031: 1 << 44, 1022: 1 << 45, 1011: 1 << 46, 992: 1 << 47,
              1095: 1 << 48, 2195: 1 << 49, 3296: 1 << 50}
    need(not set(label) & set(legacy), 'disjoint old label/marker families')
    for e in range(943, 3297):
        need(old[e] == label.get(e, legacy.get(e, 0)), 'every OLD control and unlisted zero')
    changed = old.copy()
    # Independent full OLD-array transformation, not the direct coordinate formula.
    for i in range(943):
        changed[i] = (1 << 44) + 1026 - old[i]
    for e in label:
        changed[e] = old[e]
    for e in REMOVED:
        changed[e] = 0
    for e in ANCHORS:
        changed[e] = 1 << 44
    for e in range(943, 3297):
        expected = old[e] if e in label else (1 << 44) if e in ANCHORS else 0
        need(changed[e] == expected, 'every transformed control and unlisted zero')
    return old, changed


def verify_model(model):
    need(type(model) is dict and set(model) == {'old_tiles', 'positive_tiles', 'controls', 'k_raw'},
         'entire actual model schema')
    check_color_complement(model['old_tiles'], model['positive_tiles'])
    left = direct_phi(model['positive_tiles'], model['controls'])
    old, right = recovered_phi(model['k_raw'])
    need(left == right, 'all 3297 NEW coefficients and ordered selectors')
    need(len({tuple(t) for t in model['old_tiles']}) == 943
         and len({tuple(t) for t in model['positive_tiles']}) == 943, 'all distinct old and positive tiles')
    need(model['old_tiles'][0] == [2, 435, 3, 1] and model['old_tiles'][1] == [5, 0, 0, 0]
         and model['old_tiles'][929] == [3, 436, 4, 4], 'old Start/Forbidden/initializer binding')
    need(model['positive_tiles'][0] == [253, 76, 252, 510]
         and model['positive_tiles'][1] == [250, 511, 255, 511]
         and model['positive_tiles'][929] == [252, 75, 251, 507],
         'complemented Start/Forbidden/initializer binding')
    association = {'old_array_sha256': digest(encode(old)), 'new_array_sha256': digest(encode(left)),
                   'old_tiles_sha256': digest(encode(model['old_tiles'])),
                   'positive_tiles_sha256': digest(encode(model['positive_tiles'])),
                   'coefficients_compared': 3297, 'ordered_tiles': 943, 'label_controls': 34,
                   'anchor_assignments': 3, 'selector_spacing_bits': 10,
                   'positive_color_complement_maxima': list(COMPLEMENT),
                   'removed_occupancy_positions': list(REMOVED),
                   'nonzero_coefficients': 980, 'zero_dummy_positions': [1063, 1064]}
    return left, right, association


def check_association(association, model):
    need(typed_equal(association, verify_model(model)[2]), 'entire whole-model route association')


def binary_power(a, exponent, modulus):
    result = 1
    a %= modulus
    while exponent:
        if exponent & 1:
            result = result * a % modulus
        a = a * a % modulus
        exponent //= 2
    return result


def inverse_route(phi, modulus):
    rho = pow(2, BITS, modulus)
    b = pow(rho, CELL, modulus)
    power, value = 1, 0
    inverse = pow(rho, -1, modulus)
    for c in phi:
        value = (value + c * power) % modulus
        power = power * inverse % modulus
    k = (sum(pow(rho, e, modulus) for e in (30, 62, 1100, 2201, 8849))
         + (pow(rho, 4393, modulus) + pow(rho, 5495, modulus)) * value) % modulus
    h = (1 + b * k + b * b) % modulus
    return {'modulus': modulus, 'rho_mod': rho, 'B_mod': b, 'K_mod': k, 'Hctrl_mod': h,
            'unit': gcd(h, modulus) == 1, 'whole_phi_sha256': digest(encode(phi))}


def positive_route(phi, modulus):
    rho = binary_power(2, BITS, modulus)
    b = binary_power(rho, CELL, modulus)
    value = 0
    for c in phi:
        value = (value * rho + c) % modulus
    dc = (sum(binary_power(rho, e, modulus) for e in (30, 62, 1100, 2201))
          + binary_power(rho, 1097, modulus) * (1 + binary_power(rho, 1102, modulus)) * value) % modulus
    dr = binary_power(rho, 42, modulus)
    k = (dc + b * dr) % modulus
    h = (1 + b * dc + b * b * (dr + 1)) % modulus
    return {'modulus': modulus, 'rho_mod': rho, 'B_mod': b, 'K_mod': k, 'Hctrl_mod': h,
            'unit': gcd(h, modulus) == 1, 'whole_phi_sha256': digest(encode(phi))}


def check_bracket(cert, phi, modulus):
    need(typed_equal(cert, positive_route(phi, modulus)), 'whole two-route bracket and array association')


def primality_certificate(n):
    divisor = 2 if n > 2 and n % 2 == 0 else None
    for a in range(3, isqrt(n) + 1, 2):
        if divisor is None and n % a == 0:
            divisor = a
            break
    return {'n': n, 'limit': isqrt(n), 'prime': divisor is None, 'least_divisor': divisor}


def check_primality(cert, n):
    need(type(n) is int and n > 1, 'prime argument scope')
    need(type(cert) is dict and set(cert) == {'n', 'limit', 'prime', 'least_divisor'}
         and type(cert['n']) is int and cert['n'] == n and type(cert['limit']) is int
         and cert['limit'] == isqrt(n) and type(cert['prime']) is bool, 'strict prime certificate schema')
    divisor = next((a for a in range(2, isqrt(n) + 1) if n % a == 0), None)
    need(typed_equal(cert['least_divisor'], divisor) and cert['prime'] is (divisor is None),
         'complete trial-division certificate')


def factors(n):
    result, a = [], 2
    while a * a <= n:
        exponent = 0
        while n % a == 0:
            n //= a
            exponent += 1
        if exponent:
            result.append([a, exponent])
        a += 1
    if n > 1:
        result.append([n, 1])
    return result


def order_certificate(modulus, bound, exponent=D):
    b, order = pow(2, exponent, modulus), bound
    for q, _ in factors(bound):
        while order % q == 0 and pow(b, order // q, modulus) == 1:
            order //= q
    fs = factors(order)
    return {'modulus': modulus, 'group_bound': bound, 'base_exponent': exponent, 'B_mod': b, 'order': order, 'factors': fs,
            'annihilating_residue': pow(b, order, modulus),
            'proper_residues': [{'prime': q, 'residue': pow(b, order // q, modulus)} for q, _ in fs],
            'B_squared_mod': b * b % modulus, 'square_unit': gcd(b * b - 1, modulus) == 1}


def check_order(cert, modulus, bound, exponent=D):
    need(type(cert) is dict and set(cert) == {'modulus', 'group_bound', 'base_exponent', 'B_mod', 'order', 'factors',
         'annihilating_residue', 'proper_residues', 'B_squared_mod', 'square_unit'}
         and all(type(cert[k]) is int for k in ['modulus', 'group_bound', 'base_exponent', 'B_mod', 'order',
                                               'annihilating_residue', 'B_squared_mod'])
         and cert['modulus'] == modulus and cert['group_bound'] == bound and cert['base_exponent'] == exponent
         and 1 <= cert['order'] <= bound and bound % cert['order'] == 0
         and type(cert['square_unit']) is bool, 'strict order certificate schema/context')
    b = binary_power(2, exponent, modulus)
    need(cert['B_mod'] == b and cert['annihilating_residue'] == binary_power(b, cert['order'], modulus) == 1,
         'order certificate annihilating power')
    need(type(cert['factors']) is list, 'order factor list')
    product, qs = 1, set()
    for item in cert['factors']:
        need(type(item) is list and len(item) == 2 and all(type(v) is int for v in item), 'strict order factor pair')
        q, multiplicity = item
        need(2 <= q <= cert['order'] and 1 <= multiplicity <= cert['order'].bit_length() and q not in qs
             and all(q % a for a in range(2, isqrt(q) + 1)), 'order factors distinct primes')
        product *= q ** multiplicity
        qs.add(q)
    need(product == cert['order'], 'complete order prime factorization')
    need(type(cert['proper_residues']) is list and len(cert['proper_residues']) == len(qs),
         'all proper-power witnesses')
    seen = set()
    for row in cert['proper_residues']:
        need(type(row) is dict and set(row) == {'prime', 'residue'}
             and type(row['prime']) is int and type(row['residue']) is int
             and row['prime'] in qs and row['prime'] not in seen, 'strict proper-power witness')
        value = binary_power(b, cert['order'] // row['prime'], modulus)
        need(row['residue'] == value and value != 1, 'order certificate nontrivial proper power')
        seen.add(row['prime'])
    need(cert['B_squared_mod'] == b * b % modulus
         and cert['square_unit'] is (gcd(b * b - 1, modulus) == 1), 'exact square-unit certificate')


def lift_certificate(prime, exponent=D):
    residue = pow(pow(2, exponent, prime * prime), prime - 1, prime * prime)
    return {'prime': prime, 'kappa': prime - 1, 'base_exponent': exponent, 'modulus': prime * prime, 'residue': residue,
            'valuation_one': residue % prime == 1 and residue != 1}


def check_lift(cert, prime, exponent=D):
    need(type(cert) is dict and set(cert) == {'prime', 'kappa', 'base_exponent', 'modulus', 'residue', 'valuation_one'}
         and all(type(cert[k]) is int for k in ['prime', 'kappa', 'base_exponent', 'modulus', 'residue'])
         and cert['prime'] == prime and cert['kappa'] == prime - 1 and cert['base_exponent'] == exponent
         and cert['modulus'] == prime * prime
         and type(cert['valuation_one']) is bool, 'strict lambda-squared lift schema')
    value = binary_power(2, exponent * (prime - 1), prime * prime)
    need(cert['residue'] == value and value % prime == 1, 'exact lambda-squared lift residue')
    need(cert['valuation_one'] is (value != 1), 'exact valuation-one flag')


def fixed_bundle(left):
    return {'spacing': STEP,
            'prime_rows': [{'prime': p, 'primality': primality_certificate(p),
                            'order': order_certificate(p, p - 1), 'inverse_route': inverse_route(left, p)}
                           for p in FIXED]}


def check_fixed(fixed, right):
    need(type(fixed) is dict and set(fixed) == {'spacing', 'prime_rows'}
         and type(fixed['spacing']) is int and fixed['spacing'] == STEP
         and type(fixed['prime_rows']) is list and len(fixed['prime_rows']) == 2, 'strict fixed bundle schema')
    for row, p, exact in zip(fixed['prime_rows'], FIXED, (23, 4403)):
        need(type(row) is dict and set(row) == {'prime', 'primality', 'order', 'inverse_route'}
             and type(row['prime']) is int and row['prime'] == p, 'exact fixed prime context')
        check_primality(row['primality'], p)
        need(row['primality']['prime'], 'fixed modulus certified prime')
        check_order(row['order'], p, p - 1)
        need(row['order']['order'] == exact, 'exact fixed prime order')
        check_bracket(row['inverse_route'], right, p)
    need(STEP == 23 * 4403 and gcd(23, 4403) == 1, 'complete spacing association')


def prime_payload(prime, left, abstract_fixture=False):
    if abstract_fixture:
        need(prime == 5, 'only declared abstract prime5 fixture')
        return {'prime': 5, 'primality': primality_certificate(5),
                'order': order_certificate(5, 4, 1), 'lift': lift_certificate(5, 1),
                'inverse_route': {'modulus': 5, 'rho_mod': 2, 'B_mod': 2, 'K_mod': 1,
                                  'Hctrl_mod': 2, 'unit': True,
                                  'whole_phi_sha256': 'abstract-B2-K1-no-Phi'}}
    return {'prime': prime, 'primality': primality_certificate(prime),
            'order': order_certificate(prime, prime - 1), 'lift': lift_certificate(prime),
            'inverse_route': inverse_route(left, prime)}


def check_prime_payload(payload, prime, right, abstract_fixture=False):
    need(type(payload) is dict and set(payload) == {'prime', 'primality', 'order', 'lift', 'inverse_route'}
         and type(payload['prime']) is int and payload['prime'] == prime, 'entire prime payload/context')
    check_primality(payload['primality'], prime)
    need(payload['primality']['prime'], 'prime payload really prime')
    if abstract_fixture:
        need(prime == 5, 'only declared abstract prime5 fixture')
        check_order(payload['order'], 5, 4, 1)
        check_lift(payload['lift'], 5, 1)
        b, k = binary_power(2, 1, 5), 1
        h = (1 + b*k + b*b) % 5
        expected = {'modulus': 5, 'rho_mod': b, 'B_mod': b, 'K_mod': k,
                    'Hctrl_mod': h, 'unit': gcd(h, 5) == 1,
                    'whole_phi_sha256': 'abstract-B2-K1-no-Phi'}
        need(typed_equal(payload['inverse_route'], expected), 'whole two-route bracket and array association')
    else:
        check_order(payload['order'], prime, prime - 1)
        check_lift(payload['lift'], prime)
        check_bracket(payload['inverse_route'], right, prime)


def failure_reasons(payload):
    reasons = []
    if not payload['order']['square_unit']:
        reasons.append('square-nonunit')
    if payload['order']['order'] <= 2:
        reasons.append('order-at-most-two')
    if not payload['lift']['valuation_one']:
        reasons.append('lift-not-valuation-one')
    if not payload['inverse_route']['unit']:
        reasons.append('bracket-nonunit')
    return reasons


def make_trial(m, left):
    p = STEP * m + 1
    prime = primality_certificate(p)
    if not prime['prime']:
        return {'m': m, 'lambda': p, 'primality': prime, 'reasons': ['composite']}
    payload = prime_payload(p, left)
    reasons = failure_reasons(payload)
    return {'m': m, 'lambda': p, 'certificate': payload, 'reasons': reasons, 'admissible': not reasons}


def check_trial(row, m, right):
    need(type(row) is dict and type(row.get('m')) is int and row['m'] == m and FIRST_M <= m <= LAST_M
         and type(row.get('lambda')) is int and row['lambda'] == STEP * m + 1 and row['lambda'] > D,
         'exact candidate parameter/prefix')
    p = row['lambda']
    if 'primality' in row:
        need(set(row) == {'m', 'lambda', 'primality', 'reasons'}, 'complete composite trial schema')
        check_primality(row['primality'], p)
        need(not row['primality']['prime'] and typed_equal(row['reasons'], ['composite']),
             'exact composite trial reason')
        return False
    need(set(row) == {'m', 'lambda', 'certificate', 'reasons', 'admissible'}, 'complete prime trial schema')
    check_prime_payload(row['certificate'], p, right)
    reasons = failure_reasons(row['certificate'])
    need(typed_equal(row['reasons'], reasons), 'every ordered candidate failure reason')
    need(type(row['admissible']) is bool and row['admissible'] is (not reasons), 'exact admissible candidate predicate')
    return not reasons


def fixed_failure_conditions(fixed):
    result = []
    for row in fixed['prime_rows']:
        if not row['order']['square_unit']:
            result.append({'modulus': row['prime'], 'condition': 'B-squared-minus-one-nonunit'})
        if not row['inverse_route']['unit']:
            result.append({'modulus': row['prime'], 'condition': 'Hctrl-nonunit'})
    return result


def fixed_conditions_hold(fixed):
    return not fixed_failure_conditions(fixed)


def check_science(science, fixed, right):
    check_fixed(fixed, right)
    need(type(science) is dict and set(science) == {'outcome', 'selected_m', 'selected_lambda',
         'conditional_premises_discharged', 'fixed_failures', 'trials'} and type(science['trials']) is list
         and type(science['conditional_premises_discharged']) is bool, 'strict scientific report schema')
    need(typed_equal(science['fixed_failures'], fixed_failure_conditions(fixed)), 'all exact fixed-premise failures')
    selected = None
    if not fixed_conditions_hold(fixed):
        need(science['trials'] == [], 'fixed-unit obstruction has no candidate search')
        outcome = 'fixed-unit-obstruction'
    else:
        need(1 <= len(science['trials']) <= LAST_M - FIRST_M + 1, 'nonempty bounded trial prefix')
        for j, row in enumerate(science['trials']):
            if check_trial(row, FIRST_M + j, right):
                need(j == len(science['trials']) - 1, 'stop exactly at first admissible candidate')
                selected = row['m']
        need(selected is not None or len(science['trials']) == LAST_M - FIRST_M + 1, 'complete bounded exhaustion')
        outcome = 'found' if selected is not None else 'NOT_FOUND'
    need(type(science['outcome']) is str and science['outcome'] == outcome, 'exact scientific outcome')
    need(typed_equal(science['selected_m'], selected), 'exact selected candidate or none')
    need(typed_equal(science['selected_lambda'], None if selected is None else STEP * selected + 1),
         'exact selected lambda or none')
    need(science['conditional_premises_discharged'] is (selected is not None), 'science is not verification flag')


def science_probe(left, right):
    fixed = fixed_bundle(left)
    check_fixed(fixed, right)
    trials, selected = [], None
    if fixed_conditions_hold(fixed):
        for m in range(FIRST_M, LAST_M + 1):
            row = make_trial(m, left)
            trials.append(row)
            if check_trial(row, m, right):
                selected = m
                break
    science = {'outcome': 'fixed-unit-obstruction' if not fixed_conditions_hold(fixed)
               else 'found' if selected is not None else 'NOT_FOUND',
               'selected_m': selected, 'selected_lambda': None if selected is None else STEP * selected + 1,
               'conditional_premises_discharged': selected is not None,
               'fixed_failures': fixed_failure_conditions(fixed), 'trials': trials}
    check_science(science, fixed, right)
    return fixed, science


def expect_rejection(name, operation, reason):
    try:
        operation()
    except ValueError as error:
        need(str(error) == reason, 'intended exact semantic control location: ' + name)
        return {'name': name, 'reason': str(error)}
    raise ValueError('accepted semantic corruption: ' + name)


def controls(model, left, right, association, fixed, science):
    saved = deepcopy((model, association, fixed, science))
    rejected, valid, cases = [], [], []
    changed = deepcopy(model); changed['old_tiles'][2][0] ^= 1
    changed['positive_tiles'][2][0] = 255 - changed['old_tiles'][2][0]
    cases.append(('old-tile-coordinate-with-complement', changed, 'all 3297 NEW coefficients and ordered selectors'))
    changed = deepcopy(model)
    for key in ['old_tiles', 'positive_tiles']:
        changed[key][2], changed[key][3] = changed[key][3], changed[key][2]
    cases.append(('old-and-positive-tile-order', changed, 'all 3297 NEW coefficients and ordered selectors'))
    changed = deepcopy(model); changed['old_tiles'][2][0] = True
    cases.append(('boolean-old-tile', changed, 'integer old four-coordinate tile'))
    changed = deepcopy(model); changed['positive_tiles'][2][0] = True
    cases.append(('boolean-positive-tile', changed, 'integer positive four-coordinate tile'))
    changed = deepcopy(model); changed['positive_tiles'] = deepcopy(changed['old_tiles'])
    cases.append(('missing-positive-color-complement', changed, 'whole positive color complement'))
    changed = deepcopy(model); changed['positive_tiles'][2][0] += 1
    cases.append(('wrong-positive-color-complement', changed, 'whole positive color complement'))
    changed = deepcopy(model); changed['controls'].pop(0)
    cases.append(('missing-label-control', changed, 'whole new Phi support'))
    changed = deepcopy(model)
    for pair in changed['controls']:
        if pair[0] not in ANCHORS:
            pair[1] *= 2
    cases.append(('wrong-eleven-bit-label-spacing', changed, 'all 3297 NEW coefficients and ordered selectors'))
    for e in REMOVED:
        changed = deepcopy(model); changed['controls'].append([e, 1 << 44])
        cases.append(('removed-occupancy-' + str(e), changed, 'whole new Phi support'))
    for e in [1023, 1003, 1013, 983]:
        changed = deepcopy(model)
        for pair in changed['controls']:
            if pair[0] == e:
                pair[1] += 1
        cases.append(('label-family-' + str(e), changed, 'all 3297 NEW coefficients and ordered selectors'))
    for e in ANCHORS:
        changed = deepcopy(model)
        for pair in changed['controls']:
            if pair[0] == e:
                pair[1] //= 2
        cases.append(('anchor-weight-' + str(e), changed, 'all 3297 NEW coefficients and ordered selectors'))
    for e in [1063, 1064]:
        changed = deepcopy(model); changed['controls'].append([e, 1])
        cases.append(('dummy-hole-' + str(e), changed, 'both zero dummy holes'))
    changed = deepcopy(model); changed['controls'].append([1062, 1])
    cases.append(('unlisted-zero', changed, 'whole new Phi support'))
    changed = deepcopy(model); changed['k_raw'] = bytes([changed['k_raw'][0] ^ 1]) + changed['k_raw'][1:]
    cases.append(('old-K-low-bit', changed, 'existing K first exact factor'))
    changed = deepcopy(model); changed['k_raw'] += b'\0'
    cases.append(('old-K-nonminimal', changed, 'minimal K little-endian encoding'))
    for name, changed, reason in cases:
        rejected.append(expect_rejection(name, lambda m=changed: verify_model(m), reason))
    changed = dict(association); h = changed['new_array_sha256']; changed['new_array_sha256'] = ('1' if h[0] == '0' else '0') + h[1:]
    rejected.append(expect_rejection('whole-model-array-association',
                    lambda: check_association(changed, model),
                    'entire whole-model route association'))
    cases = []
    changed = deepcopy(fixed); changed['prime_rows'][0]['order'].update(modulus=49, group_bound=42)
    cases.append(('old-composite49-order-context', changed, 'strict order certificate schema/context'))
    changed = deepcopy(fixed); changed['prime_rows'][0]['order'].update(order=1, factors=[], proper_residues=[])
    cases.append(('mod47-order-one', changed, 'order certificate annihilating power'))
    changed = deepcopy(fixed); changed['prime_rows'][0]['order']['factors'].pop()
    cases.append(('missing-mod47-factor', changed, 'complete order prime factorization'))
    changed = deepcopy(fixed); changed['prime_rows'][0]['order']['proper_residues'][0]['residue'] ^= 1
    cases.append(('mod47-proper-power', changed, 'order certificate nontrivial proper power'))
    changed = deepcopy(fixed); changed['prime_rows'][0]['order']['order'] = True
    cases.append(('boolean-order', changed, 'strict order certificate schema/context'))
    changed = deepcopy(fixed); row = changed['prime_rows'][0]['order']; row['square_unit'] = not row['square_unit']
    cases.append(('mod47-square-unit-flag', changed, 'exact square-unit certificate'))
    changed = deepcopy(fixed); changed['prime_rows'][0]['primality']['prime'] = False
    cases.append(('false-fixed-primality', changed, 'complete trial-division certificate'))
    changed = deepcopy(fixed); changed['prime_rows'][0]['primality']['n'] = True
    cases.append(('boolean-fixed-prime', changed, 'strict prime certificate schema'))
    for j, p in enumerate(FIXED):
        changed = deepcopy(fixed); row = changed['prime_rows'][j]['inverse_route']; row['Hctrl_mod'] = (row['Hctrl_mod'] + 1) % p
        cases.append(('fixed-Hctrl-' + str(p), changed, 'whole two-route bracket and array association'))
        changed = deepcopy(fixed); row = changed['prime_rows'][j]['inverse_route']; row['unit'] = not row['unit']
        cases.append(('fixed-unit-' + str(p), changed, 'whole two-route bracket and array association'))
    changed = deepcopy(fixed); h = changed['prime_rows'][0]['inverse_route']['whole_phi_sha256']
    changed['prime_rows'][0]['inverse_route']['whole_phi_sha256'] = ('1' if h[0] == '0' else '0') + h[1:]
    cases.append(('fixed-whole-Phi-association', changed, 'whole two-route bracket and array association'))
    for name, changed, reason in cases:
        rejected.append(expect_rejection(name, lambda f=changed: check_fixed(f, right), reason))
    prime_trials = [r for r in science['trials'] if 'certificate' in r]
    # If no admissible real prime is selected, use a labeled
    # abstract prime5/B2/K1 fixture through the SAME prime-payload checker. It is
    # neither an admissible lambda nor an extra candidate-search interval.
    admissible_trials = [r for r in prime_trials if r['admissible']]
    abstract_fixture = not bool(admissible_trials)
    fixture = deepcopy(admissible_trials[0]['certificate']) if admissible_trials else prime_payload(5, left, True)
    p = fixture['prime']
    check_prime_payload(fixture, p, right, abstract_fixture)
    if abstract_fixture:
        need(not failure_reasons(fixture), 'complete positive abstract prime fixture')
    payload_cases = []
    changed = deepcopy(fixture); changed['prime'] += 1
    payload_cases.append(('lambda-context', changed, 'entire prime payload/context'))
    changed = deepcopy(fixture); changed['lift']['modulus'] += 1
    payload_cases.append(('lambda-squared-modulus', changed, 'strict lambda-squared lift schema'))
    changed = deepcopy(fixture); changed['lift']['residue'] = (changed['lift']['residue'] + 1) % changed['lift']['modulus']
    payload_cases.append(('lambda-squared-residue', changed, 'exact lambda-squared lift residue'))
    changed = deepcopy(fixture); changed['lift']['valuation_one'] = not changed['lift']['valuation_one']
    payload_cases.append(('lambda-lift-flag', changed, 'exact valuation-one flag'))
    changed = deepcopy(fixture); changed['order']['factors'].pop()
    payload_cases.append(('lambda-missing-factor', changed, 'complete order prime factorization'))
    changed = deepcopy(fixture); changed['order']['square_unit'] = not changed['order']['square_unit']
    payload_cases.append(('lambda-square-unit-flag', changed, 'exact square-unit certificate'))
    changed = deepcopy(fixture); r = changed['inverse_route']; r['Hctrl_mod'] = (r['Hctrl_mod'] + 1) % p
    payload_cases.append(('lambda-Hctrl', changed, 'whole two-route bracket and array association'))
    changed = deepcopy(fixture); r = changed['inverse_route']; r['unit'] = not r['unit']
    payload_cases.append(('lambda-unit-flag', changed, 'whole two-route bracket and array association'))
    for name, changed, reason in payload_cases:
        rejected.append(expect_rejection(name, lambda r=changed: check_prime_payload(r, p, right, abstract_fixture), reason))
    for name, field, value, reason in [
            ('science-outcome', 'outcome', 'NOT_FOUND' if science['outcome'] != 'NOT_FOUND' else 'found', 'exact scientific outcome'),
            ('science-selection', 'selected_m', LAST_M + 1, 'exact selected candidate or none'),
            ('science-lambda', 'selected_lambda', 1, 'exact selected lambda or none'),
            ('science-not-PASS', 'conditional_premises_discharged', not science['conditional_premises_discharged'], 'science is not verification flag'),
            ('science-fixed-failures', 'fixed_failures', [{'modulus': 0, 'condition': 'invented'}], 'all exact fixed-premise failures')]:
        changed = deepcopy(science); changed[field] = value
        rejected.append(expect_rejection(name, lambda s=changed: check_science(s, fixed, right), reason))
    changed = deepcopy(science)
    if changed['trials']:
        changed['trials'][0]['m'] += 1
        reason = 'exact candidate parameter/prefix'
    else:
        changed['trials'].append({})
        reason = 'fixed-unit obstruction has no candidate search'
    rejected.append(expect_rejection('actual-prefix-or-forbidden-search',
                    lambda: check_science(changed, fixed, right), reason))
    changed = deepcopy(model); changed['controls'].reverse(); verify_model(changed); valid.append('control-contribution-order')
    changed = deepcopy(model); e, c = changed['controls'][0]; changed['controls'][0] = [e, c-1]; changed['controls'].append([e, 1])
    verify_model(changed); valid.append('exact-control-contribution-split')
    changed = deepcopy(fixed)
    for r in [v['order'] for v in changed['prime_rows']]:
        r['factors'].reverse(); r['proper_residues'].reverse()
    check_fixed(changed, right); valid.append('factor-and-proper-witness-order')
    changed = json.loads(encode(fixture), object_pairs_hook=unique_object, parse_constant=reject_constant)
    check_prime_payload(changed, p, right, abstract_fixture); valid.append('whole-typed-prime-certificate-round-trip')
    need(len(rejected) == 52 and len(valid) == 4, 'all exact control counts')
    need(typed_equal((model, association, fixed, science), saved), 'controls preserve original actual models')
    return {'negative': rejected, 'negative_count': len(rejected), 'valid': valid, 'valid_count': len(valid),
            'prime_payload_fixture': 'actual-selected-admissible-prime' if admissible_trials else 'abstract-prime5-exponent1-B2-K1-not-actual47-lambda',
            'actual_search_prime_branch_exercised': bool(prime_trials), 'fixture_modulus': p,
            'abstract_fixture_used': abstract_fixture,
            'complete_prime_payload_fixture_certificate': fixture,
            'synthetic_fixture_discharges_no_candidate_premise': True}


def main():
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    provenance = authenticate()
    output = receipt_path(args.output)
    ports, raw = existing_ports()
    old_tiles = load(INDEXED / 'TILES.json')
    need(type(old_tiles) is list and all(type(t) is list and all(type(v) is int for v in t) for t in old_tiles),
         'typed existing tile source before color complement')
    model = {'old_tiles': old_tiles,
             'positive_tiles': [[maximum - v for maximum, v in zip(COMPLEMENT, t)] for t in old_tiles],
             'controls': new_controls(), 'k_raw': raw}
    need(len(model['controls']) == 37, 'all34 label and three anchor contributions')
    left, right, association = verify_model(model)
    check_association(association, model)
    fixed, science = science_probe(left, right)
    checked = controls(model, left, right, association, fixed, science)
    moduli = set(FIXED) | {r['lambda'] for r in science['trials'] if 'certificate' in r}
    report = {'schema': 'complemented_three_anchor47_bounded_controller_certificate_v1', 'status': 'PASS',
              'optimized_python': bool(sys.flags.optimize), 'provenance': provenance, 'question': QUESTION,
              'existing_coherent_ports': ports, 'old_raw_port_bytes': 295388,
              'whole_Phi_association': association, 'fixed_certificates': fixed, 'scientific_result': science,
              'independent_positive_modular_certificates': [positive_route(right, p) for p in sorted(moduli)],
              'controls': checked, 'scientific_success_is_not_verification_success': True,
              'no_new47_B_K_masks_tuple_native_source_endpoint_or_page': True,
              'scope': 'Only accepted complemented conditional47 finite controller premises and bounded m5..205. No unbounded prime existence, tuple/source/P66/native/compiler/Lean/PDF or minimum claim.'}
    need(authenticate() == provenance, 'all held/external/runtime bytes unchanged')
    receipt_path(args.output)
    raw_report = encode(report)
    with output.open('xb') as stream:
        stream.write(raw_report)
    sys.stdout.write(raw_report.decode())


if __name__ == '__main__':
    main()

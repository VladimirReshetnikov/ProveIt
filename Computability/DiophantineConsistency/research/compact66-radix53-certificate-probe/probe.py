#!/usr/bin/env python3
"""CODE ONLY/HOLD: bounded radix53 prime/order/lift and full-Phi probe."""
import sys

sys.dont_write_bytecode = True

import argparse
from copy import deepcopy
import gzip
from hashlib import sha256
import json
from math import isqrt
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REPO = ROOT.parents[1]
COMPACT = ROOT / 'candidates/one-page-compact66'
INDEXED = ROOT / 'research/indexed-tile-enumeration'
TEMPLATE = 'research/compact66-radix65-unit-probe'
PARENTS = {'candidates/one-page-compact66', 'research/indexed-tile-enumeration',
           'research/compact66-radix-boundary', 'research/compact66-radix65-native-adapter',
           'research/compact66-radix65-unit-probe-verification',
           'research/compact66-radix53-carry-tolerance'}
PAYLOADS = {'probe.py', 'README.md', 'PROOF.md', 'TOOLCHAIN.md', 'SOURCE_PINS.json'}
BITS, CELL, D, STEP, FIRST_M, LAST_M = 53, 8807, 466771, 228956, 3, 66
FIXED = (53, 8807)
QUESTION = {'radix_bits': 53, 'cell_digits': 8807, 'd': 466771,
            'candidate_step': 228956, 'first_m': 3, 'last_m': 66,
            'fixed_unit_primes': [53, 8807], 'all_unit_values_unknown_in_preparation': True,
            'existence_or_nonzero_not_a_verification_gate': True}
STEM = '/tmp/compact66-radix53-certificate-probe-'
OUTPUTS = {False: (STEM + 'normal.json', STEM + 'root-normal.json'),
           True: (STEM + 'optimized.json', STEM + 'root-optimized.json')}


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
         and held['schema'] == 'radix53_certificate_probe_hold_v1' and type(held['scope']) is str
         and type(held['payload_files']) is int and held['payload_files'] == 5
         and type(held['payload_bytes']) is int
         and held['payload_bytes'] == sum(x['bytes'] for x in members.values()), 'strict held schema/census')
    pins = load(ordinary_path(HERE, 'SOURCE_PINS.json'))
    need(type(pins) is dict and set(pins) == {'schema', 'path_base', 'scope', 'question', 'files',
         'own_core', 'closed_parents', 'readonly_template', 'python'}
         and pins['schema'] == 'radix53_certificate_probe_pins_v1'
         and pins['path_base'] == 'Computability/DiophantineConsistency'
         and type(pins['scope']) is str and typed_equal(pins['question'], QUESTION), 'strict pin question/schema')
    need(type(pins['own_core']) is dict and set(pins['own_core']) == PAYLOADS - {'SOURCE_PINS.json'},
         'complete own code/prose pins')
    for name, expected in pins['own_core'].items():
        need(record(ordinary_path(HERE, name)) == checked_record(expected), 'own core: ' + name)
    need(type(pins['files']) is dict, 'flat external pin mapping')
    for name, expected in pins['files'].items():
        need(record(ordinary_path(ROOT, name)) == checked_record(expected), 'external whole file: ' + name)
    need(type(pins['closed_parents']) is dict and set(pins['closed_parents']) == PARENTS, 'exact six parents')
    parents = {}
    for relative, expected in pins['closed_parents'].items():
        folder = ROOT / relative
        need(record(ordinary_path(ROOT, relative + '/MANIFEST.json')) == checked_record(expected), 'parent seal')
        _, files = whole_inventory(folder, 'MANIFEST.json')
        for name, value in files.items():
            need(pins['files'].get(relative + '/' + name) == value, 'every parent payload flattened')
        need(pins['files'].get(relative + '/MANIFEST.json') == expected, 'parent manifest flattened')
        parents[relative] = {'manifest': expected, 'payloads': len(files),
                             'payload_bytes': sum(v['bytes'] for v in files.values())}
    template = pins['readonly_template']
    need(type(template) is dict and set(template) == {'folder', 'inventory'}
         and template['folder'] == TEMPLATE, 'exact read-only template policy')
    need(record(ordinary_path(ROOT, TEMPLATE + '/HOLD_INVENTORY.json'))
         == checked_record(template['inventory']), 'template inventory')
    _, files = whole_inventory(ROOT / TEMPLATE, 'HOLD_INVENTORY.json', PAYLOADS)
    for name, value in files.items():
        need(pins['files'].get(TEMPLATE + '/' + name) == value, 'template payload flattened')
    need(pins['files'].get(TEMPLATE + '/HOLD_INVENTORY.json') == template['inventory'], 'template seal flattened')
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


def control_terms():
    return ([(1023+j, 1 << (10+j)) for j in range(8)]
            + [(1003+j, 1 << (27+j)) for j in range(8)]
            + [(1013+j, 1 << (18+j)) for j in range(9)]
            + [(983+j, 1 << (35+j)) for j in range(9)]
            + [(1031, 1 << 44), (1022, 1 << 45), (1011, 1 << 46), (992, 1 << 47),
               (1095, 1 << 48), (2195, 1 << 49), (3296, 1 << 50)])


def phi_tiles(tiles, controls):
    need(type(tiles) is list and len(tiles) == 943, 'exact ordered tile list')
    phi = [0] * 3297
    for i, tile in enumerate(tiles):
        need(type(tile) is list and len(tile) == 4 and all(type(v) is int for v in tile), 'integer four-coordinate tile')
        w, n, p, s = tile
        need(0 <= w < 256 and 0 <= n < 512 and 0 <= p < 256 and 0 <= s < 512, 'every tile field bound')
        phi[i] = 1 + (1 << 10) * ((1 << 34) - w - (n << 8) - (p << 17) - (s << 25))
        need(0 < phi[i] < 1 << 45, 'selector coefficient bound')
    for e, c in controls:
        need(type(e) is int and type(c) is int and 943 <= e <= 3296 and c > 0, 'control contribution type/range')
        phi[e] += c
    need(phi[1063] == phi[1064] == 0, 'both zero dummy holes')
    support = set(range(943)) | set(range(983, 993)) | set(range(1003, 1012)) | set(range(1013, 1032))
    support |= {1095, 2195, 3296}
    need({e for e, c in enumerate(phi) if c} == support and len(support) == 984, 'whole Phi support')
    need(all(0 <= c < 1 << 67 for c in phi), 'old-radix digit bounds')
    return phi


def phi_old_k(raw):
    need(type(raw) is bytes and raw and raw[-1] != 0, 'minimal K little-endian encoding')
    k = int.from_bytes(raw, 'little')
    need(k.bit_length() == 592884 and len(raw) == 74111, 'whole existing K size')
    tail = k - sum(1 << (67 * e) for e in (30, 62, 1100, 2201, 8849))
    need(tail > 0, 'positive old K tail')
    tail, remainder = divmod(tail, 1 << (67 * 1097))
    need(remainder == 0, 'existing K first exact factor')
    tail, remainder = divmod(tail, 1 + (1 << (67 * 1102)))
    need(remainder == 0, 'existing K second exact factor')
    digits = []
    for _ in range(3297):
        digits.append(tail & ((1 << 67) - 1))
        tail >>= 67
    need(tail == 0, 'whole old reversed polynomial')
    return list(reversed(digits))


def verify_model(model):
    left = phi_tiles(model['tiles'], model['controls'])
    right = phi_old_k(model['k_raw'])
    need(left == right, 'all 3297 Phi coefficients and ordered selectors')
    need(len({tuple(t) for t in model['tiles']}) == 943, 'all distinct tiles')
    need(model['tiles'][0] == [2, 435, 3, 1] and model['tiles'][1] == [5, 0, 0, 0]
         and model['tiles'][929] == [3, 436, 4, 4], 'Start/Forbidden/initializer binding')
    return left, right


def binary_power(a, exponent, modulus):
    result = 1
    a %= modulus
    while exponent:
        if exponent & 1:
            result = result * a % modulus
        a = a * a % modulus
        exponent //= 2
    return result


def inverse_route(phi, prime):
    rho = pow(2, BITS, prime)
    inverse = pow(rho, -1, prime)
    b = pow(rho, CELL, prime)
    value, power = 0, 1
    for c in phi:
        value = (value + c * power) % prime
        power = power * inverse % prime
    k = (sum(pow(rho, e, prime) for e in (30, 62, 1100, 2201, 8849))
         + (pow(rho, 4393, prime) + pow(rho, 5495, prime)) * value) % prime
    h = (1 + b * k + b * b) % prime
    return {'prime': prime, 'rho_mod': rho, 'B_mod': b, 'K_mod': k, 'Hctrl_mod': h, 'unit': h != 0}


def positive_route(phi, prime):
    rho = binary_power(2, BITS, prime)
    b = binary_power(rho, CELL, prime)
    value = 0
    for c in phi:
        value = (value * rho + c) % prime
    dc = (sum(binary_power(rho, e, prime) for e in (30, 62, 1100, 2201))
          + binary_power(rho, 1097, prime) * (1 + binary_power(rho, 1102, prime)) * value) % prime
    dr = binary_power(rho, 42, prime)
    k = (dc + b * dr) % prime
    h = (1 + b * dc + b * b * (dr + 1)) % prime
    return {'prime': prime, 'rho_mod': rho, 'B_mod': b, 'K_mod': k, 'Hctrl_mod': h, 'unit': h != 0}


def check_bracket(value, expected):
    need(typed_equal(value, expected), 'whole two-route bracket certificate')


def primality_certificate(n):
    divisor = 2 if n % 2 == 0 else None
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
    # Independent verifier visits EVERY integer divisor, including all evens.
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


def order_certificate(prime):
    b, order = pow(2, D, prime), prime - 1
    for q, _ in factors(prime - 1):
        while order % q == 0 and pow(b, order // q, prime) == 1:
            order //= q
    return {'prime': prime, 'B_mod': b, 'order': order, 'factors': factors(order),
            'annihilating_residue': pow(b, order, prime),
            'proper_residues': [{'prime': q, 'residue': pow(b, order // q, prime)} for q, _ in factors(order)],
            'B_squared_mod': b * b % prime, 'square_unit': b * b % prime != 1}


def check_order(cert, prime):
    need(type(cert) is dict and set(cert) == {'prime', 'B_mod', 'order', 'factors',
         'annihilating_residue', 'proper_residues', 'B_squared_mod', 'square_unit'}
         and all(type(cert[k]) is int for k in ['prime', 'B_mod', 'order', 'annihilating_residue', 'B_squared_mod'])
         and cert['prime'] == prime and 1 <= cert['order'] <= prime - 1
         and (prime - 1) % cert['order'] == 0 and type(cert['square_unit']) is bool, 'strict order certificate schema')
    b = binary_power(2, D, prime)
    need(cert['B_mod'] == b and cert['annihilating_residue'] == binary_power(b, cert['order'], prime) == 1,
         'order certificate annihilating power')
    need(type(cert['factors']) is list, 'order factor list')
    product, qs = 1, set()
    for item in cert['factors']:
        need(type(item) is list and len(item) == 2 and all(type(v) is int for v in item), 'strict order factor pair')
        q, exponent = item
        need(2 <= q <= cert['order'] and 1 <= exponent <= cert['order'].bit_length() and q not in qs
             and all(q % a for a in range(2, isqrt(q) + 1)), 'order factors distinct primes')
        product *= q ** exponent
        qs.add(q)
    need(product == cert['order'], 'complete order prime factorization')
    need(type(cert['proper_residues']) is list and len(cert['proper_residues']) == len(qs), 'all proper-power witnesses')
    seen = set()
    for row in cert['proper_residues']:
        need(type(row) is dict and set(row) == {'prime', 'residue'}
             and type(row['prime']) is int and type(row['residue']) is int
             and row['prime'] in qs and row['prime'] not in seen, 'strict proper-power witness')
        expected = binary_power(b, cert['order'] // row['prime'], prime)
        need(row['residue'] == expected and expected != 1, 'order certificate nontrivial proper power')
        seen.add(row['prime'])
    need(cert['B_squared_mod'] == b * b % prime and cert['square_unit'] is (b * b % prime != 1),
         'exact square-unit certificate')


def lift_certificate(prime):
    residue = pow(pow(2, D, prime * prime), prime - 1, prime * prime)
    return {'prime': prime, 'kappa': prime - 1, 'modulus': prime * prime,
            'residue': residue, 'valuation_one': residue % prime == 1 and residue != 1}


def check_lift(cert, prime):
    need(type(cert) is dict and set(cert) == {'prime', 'kappa', 'modulus', 'residue', 'valuation_one'}
         and all(type(cert[k]) is int for k in ['prime', 'kappa', 'modulus', 'residue'])
         and cert['prime'] == prime and cert['kappa'] == prime - 1
         and cert['modulus'] == prime * prime and type(cert['valuation_one']) is bool, 'strict lambda-squared lift schema')
    residue = binary_power(2, D * (prime - 1), prime * prime)
    need(cert['residue'] == residue and residue % prime == 1, 'exact lambda-squared lift residue')
    need(cert['valuation_one'] is (residue != 1), 'exact valuation-one flag')


def fixed_bundle(prime, left, right):
    result = {'prime': prime, 'primality': primality_certificate(prime), 'order': order_certificate(prime),
              'inverse_route': inverse_route(left, prime)}
    positive = positive_route(right, prime)
    check_fixed(result, positive)
    return result, positive


def check_fixed(row, positive):
    prime = positive['prime']
    need(type(row) is dict and set(row) == {'prime', 'primality', 'order', 'inverse_route'}
         and type(row['prime']) is int and row['prime'] == prime and prime in FIXED, 'fixed-prime bundle schema')
    check_primality(row['primality'], prime)
    need(row['primality']['prime'], 'fixed modulus certified prime')
    check_order(row['order'], prime)
    need(row['order']['order'] == (52 if prime == 53 else 4403), 'exact retained fixed order')
    check_bracket(row['inverse_route'], positive)


def check_trial(row, expected_m, positives):
    need(type(row) is dict and type(row.get('m')) is int and row['m'] == expected_m
         and FIRST_M <= expected_m <= LAST_M and type(row.get('lambda')) is int
         and row['lambda'] == STEP * expected_m + 1 and row['lambda'] > D
         and type(row.get('primality')) is dict, 'exact candidate parameter/prefix')
    prime = row['lambda']
    check_primality(row['primality'], prime)
    if not row['primality']['prime']:
        need(set(row) == {'m', 'lambda', 'primality'}, 'complete composite trial schema')
        return False
    need(set(row) == {'m', 'lambda', 'primality', 'order', 'lift', 'inverse_route', 'admissible'},
         'complete prime trial schema')
    check_order(row['order'], prime)
    check_lift(row['lift'], prime)
    check_bracket(row['inverse_route'], positives[prime])
    admissible = (row['order']['square_unit'] and row['order']['order'] > 2
                  and row['lift']['valuation_one'] and row['inverse_route']['unit'])
    need(type(row['admissible']) is bool and row['admissible'] is admissible, 'exact admissible candidate predicate')
    return admissible


def check_science(science, fixed, positives):
    need(type(science) is dict and set(science) == {'outcome', 'selected_m', 'conditional_premises_discharged', 'trials'}
         and type(science['trials']) is list and type(science['conditional_premises_discharged']) is bool,
         'strict scientific report schema')
    selected = None
    fixed_units = all(row['inverse_route']['unit'] for row in fixed)
    if not fixed_units:
        need(science['trials'] == [], 'fixed-unit obstruction has no candidate search')
        outcome = 'fixed-unit-obstruction'
    else:
        need(1 <= len(science['trials']) <= LAST_M - FIRST_M + 1, 'nonempty bounded trial prefix')
        for j, row in enumerate(science['trials']):
            admissible = check_trial(row, FIRST_M + j, positives)
            if admissible:
                need(j == len(science['trials']) - 1, 'stop exactly at first admissible candidate')
                selected = row['m']
        need(selected is not None or len(science['trials']) == LAST_M - FIRST_M + 1, 'complete bounded exhaustion')
        outcome = 'found' if selected is not None else 'bounded-exhaustion'
    need(type(science['outcome']) is str and science['outcome'] == outcome, 'exact scientific outcome')
    need(typed_equal(science['selected_m'], selected), 'exact selected candidate or none')
    need(science['conditional_premises_discharged'] is (selected is not None), 'science is not verification flag')


def science_probe(left, right):
    fixed, positives = [], {}
    for prime in FIXED:
        row, positive = fixed_bundle(prime, left, right)
        fixed.append(row)
        positives[prime] = positive
    trials, selected = [], None
    if all(row['inverse_route']['unit'] for row in fixed):
        for m in range(FIRST_M, LAST_M + 1):
            prime = STEP * m + 1
            row = {'m': m, 'lambda': prime, 'primality': primality_certificate(prime)}
            check_primality(row['primality'], prime)
            if row['primality']['prime']:
                row.update(order=order_certificate(prime), lift=lift_certificate(prime),
                           inverse_route=inverse_route(left, prime))
                positives[prime] = positive_route(right, prime)
                row['admissible'] = (row['order']['square_unit'] and row['order']['order'] > 2
                                     and row['lift']['valuation_one'] and row['inverse_route']['unit'])
            admissible = check_trial(row, m, positives)
            trials.append(row)
            if admissible:
                selected = m
                break
    outcome = ('fixed-unit-obstruction' if not all(r['inverse_route']['unit'] for r in fixed)
               else 'found' if selected is not None else 'bounded-exhaustion')
    science = {'outcome': outcome, 'selected_m': selected,
               'conditional_premises_discharged': selected is not None, 'trials': trials}
    check_science(science, fixed, positives)
    return fixed, science, positives


def expect_rejection(name, operation, expected):
    try:
        operation()
    except ValueError as error:
        need(expected in str(error), 'intended semantic control location: ' + name)
        return {'name': name, 'reason': str(error)}
    raise ValueError('accepted semantic corruption: ' + name)


def controls(model, fixed, science, positives):
    saved = deepcopy((model, fixed, science, positives))
    rejected, valid = [], []
    cases = []
    changed = deepcopy(model); changed['tiles'][2][0] ^= 1
    cases.append(('tile_coordinate', changed, 'all 3297 Phi coefficients'))
    changed = deepcopy(model); changed['tiles'][2], changed['tiles'][3] = changed['tiles'][3], changed['tiles'][2]
    cases.append(('tile_order', changed, 'all 3297 Phi coefficients'))
    changed = deepcopy(model); changed['tiles'][2][0] = True
    cases.append(('boolean_tile', changed, 'integer four-coordinate tile'))
    changed = deepcopy(model); changed['controls'].append((1063, 1))
    cases.append(('dummy_hole', changed, 'both zero dummy holes'))
    changed = deepcopy(model); e, c = changed['controls'][0]; changed['controls'][0] = (e, c + 1)
    cases.append(('control_coefficient', changed, 'all 3297 Phi coefficients'))
    changed = deepcopy(model); changed['k_raw'] = bytes([changed['k_raw'][0] ^ 1]) + changed['k_raw'][1:]
    cases.append(('old_K_low_bit', changed, 'existing K first exact factor'))
    changed = deepcopy(model); changed['k_raw'] += b'\0'
    cases.append(('nonminimal_old_K', changed, 'minimal K little-endian encoding'))
    for name, changed, reason in cases:
        rejected.append(expect_rejection(name, lambda m=changed: verify_model(m), reason))
    base, positive = fixed[0], positives[53]
    cases = []
    changed = deepcopy(base); changed['primality']['limit'] += 1
    cases.append(('prime_trial_bound', changed, 'strict prime certificate schema'))
    changed = deepcopy(base); changed['primality']['prime'] = False
    cases.append(('false_prime_classification', changed, 'complete trial-division certificate'))
    changed = deepcopy(base); changed['primality']['n'] = True
    cases.append(('boolean_prime', changed, 'strict prime certificate schema'))
    changed = deepcopy(base); changed['order'].update(order=1, factors=[], proper_residues=[])
    cases.append(('order_one', changed, 'order certificate annihilating power'))
    changed = deepcopy(base); changed['order']['factors'].pop()
    cases.append(('missing_order_factor', changed, 'complete order prime factorization'))
    changed = deepcopy(base); changed['order']['proper_residues'][0]['residue'] ^= 1
    cases.append(('order_witness', changed, 'order certificate nontrivial proper power'))
    changed = deepcopy(base); changed['order']['square_unit'] = not changed['order']['square_unit']
    cases.append(('square_unit_flag', changed, 'exact square-unit certificate'))
    changed = deepcopy(base); changed['inverse_route']['Hctrl_mod'] = (changed['inverse_route']['Hctrl_mod'] + 1) % 53
    cases.append(('whole_bracket_residue', changed, 'whole two-route bracket certificate'))
    changed = deepcopy(base); changed['inverse_route']['unit'] = not changed['inverse_route']['unit']
    cases.append(('bracket_unit_flag', changed, 'whole two-route bracket certificate'))
    for name, changed, reason in cases:
        rejected.append(expect_rejection(name, lambda r=changed: check_fixed(r, positive), reason))
    for name, field, value, reason in [
            ('science_outcome', 'outcome', 'found' if science['outcome'] != 'found' else 'bounded-exhaustion', 'exact scientific outcome'),
            ('science_selection', 'selected_m', LAST_M + 1, 'exact selected candidate or none'),
            ('science_not_PASS', 'conditional_premises_discharged', not science['conditional_premises_discharged'], 'science is not verification flag')]:
        changed = deepcopy(science); changed[field] = value
        rejected.append(expect_rejection(name, lambda s=changed: check_science(s, fixed, positives), reason))
    prime_rows = [r for r in science['trials'] if r['primality']['prime']]
    if prime_rows:
        base = prime_rows[0]
        for name, field, value, reason in [
                ('lambda_squared_modulus', 'modulus', base['lift']['modulus'] + 1, 'strict lambda-squared lift schema'),
                ('lambda_squared_residue', 'residue', (base['lift']['residue'] + 1) % base['lift']['modulus'], 'exact lambda-squared lift residue'),
                ('lift_flag', 'valuation_one', not base['lift']['valuation_one'], 'exact valuation-one flag')]:
            changed = deepcopy(base); changed['lift'][field] = value
            rejected.append(expect_rejection(name, lambda r=changed: check_trial(r, base['m'], positives), reason))
        changed = deepcopy(base); changed['m'] += 1
        rejected.append(expect_rejection('candidate_parameter', lambda: check_trial(changed, base['m'], positives),
                                         'exact candidate parameter/prefix'))
    changed = deepcopy(model); changed['controls'].reverse(); verify_model(changed); valid.append('control_order')
    changed = deepcopy(model); e, c = changed['controls'][0]
    changed['controls'][0] = (e, c - 1); changed['controls'].append((e, 1)); verify_model(changed); valid.append('exact_control_split')
    changed = deepcopy(fixed[0]); changed['order']['factors'].reverse(); changed['order']['proper_residues'].reverse()
    check_fixed(changed, positives[53]); valid.append('order_factor_and_witness_order')
    changed = json.loads(encode(fixed[0]), object_pairs_hook=unique_object, parse_constant=reject_constant)
    check_fixed(changed, positives[53]); valid.append('complete_typed_certificate_round_trip')
    need(len(rejected) == 19 + (4 if prime_rows else 0) and len(valid) == 4, 'all branch-specific control counts')
    need((model, fixed, science, positives) == saved, 'controls preserve actual inputs and certificates')
    return {'negative': rejected, 'negative_count': len(rejected), 'valid': valid, 'valid_count': 4,
            'actual_lambda_prime_branch_controls_exercised': bool(prime_rows),
            'no_synthetic_prime_or_other_candidate_evaluation': True}


def main():
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    provenance = authenticate()
    output = receipt_path(args.output)
    ports, raw = existing_ports()
    model = {'tiles': load(INDEXED / 'TILES.json'), 'controls': control_terms(), 'k_raw': raw}
    need(len(model['controls']) == 41, 'all literal controls')
    left, right = verify_model(model)
    fixed, science, positives = science_probe(left, right)
    checked_controls = controls(model, fixed, science, positives)
    report = {'schema': 'compact66_radix53_bounded_controller_certificate_v1', 'status': 'PASS',
              'optimized_python': bool(sys.flags.optimize), 'provenance': provenance,
              'question': QUESTION, 'existing_coherent_ports': ports, 'old_raw_port_bytes': 295388,
              'phi': {'coefficients': 3297, 'ordered_tiles': 943, 'literal_controls': 41,
                      'nonzero_coefficients': 984, 'support_with_two_dummy_holes': 986,
                      'zero_dummies': [1063, 1064], 'canonical_array_sha256': digest(encode(left)),
                      'all3297_coefficients_and_ordered_bindings_equal': True},
              'fixed_certificates': fixed, 'scientific_result': science,
              'independent_positive_modular_certificates': [positives[p] for p in sorted(positives)],
              'controls': checked_controls, 'scientific_success_is_not_verification_success': True,
              'no_new_radix53_B_K_masks_tuple_native_source_endpoint_or_page': True,
              'scope': 'Only bounded finite controller premises of the accepted conditional ordinary53 proof; no unbounded existence assertion, new tuple or native/compiler/Lean replay.'}
    need(authenticate() == provenance, 'all held/external/runtime bytes unchanged')
    receipt_path(args.output)
    raw_report = encode(report)
    with output.open('xb') as stream:
        stream.write(raw_report)
    sys.stdout.write(raw_report.decode())


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Read-only exact finite verification; standard library, also under python -O."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).absolute().parent.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / 'code'))
import exact
import verify_manifest as files

PINS = {'data/PROVENANCE.json': '171ecfd318bbf0a3141d0c172a3373ee7622a84ec56e241fcf4122e33bdb7fb8', 'data/references/coefficients_0_5000.txt': '37685454a702670368480a1069ad0a44bc73ce4a262bd3688beefb3c1b556259', 'data/references/exact_checks_frozen.py': 'f09c522a20c2a23e8f2b41c0b542d45c8f9bc78a723503a38b463285aa7a3132', 'data/references/exact_results.json': '2abcc55e044a5f7d0b30668da0d8d8acf098c32bedb8ee30b32e25a51eeff7e8', 'data/references/partitions_0_10000.txt': '06705b4a96c05954e6ff81989d36c325ab34b34cc40bc931853f3bb226632f33', 'data/references/reference_hole_constants.json': '692492ea65403a4a9eb02bab7bb0124e0fa6a0591bf48012917ea92c3833afd7', 'optional/frozen_float_diagnostics.py': 'afd85461a8dbfbfd24fe01f5d7f0ae943b3594328091d547de22f8c10bae8301', 'optional/reference_results.json': '20e64deef47ac6f79001bc10ce3ae64dc3dca7ea6d4a7991a2c675762a3ba6fb'}
SCOPE = {
    'all_arithmetic_in_mandatory_core_exact': True,
    'hole_constants_pure_integer_certified': True,
    'asymptotic_remainders_certified_by_code': False,
    'effective_asymptotic_onset_certified': False,
    'finite_n_asymptotic_accuracy_certified': False,
    'general_all_orders_symbolic_engine': False,
    'convergent_all_orders_series_claimed': False,
}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def canonical(value):
    return (json.dumps(value, sort_keys=True, indent=2, ensure_ascii=True,
                       allow_nan=False) + '\n').encode('utf-8')


def read(path):
    path = Path(path).absolute()
    files.check_directory(path.parent)
    return files.read_regular(path)


def load_certificate(path):
    result = files.load_json(read(path).decode('utf-8'))
    need(type(result) is dict, 'certificate must be an object')
    return result


def same(actual, expected):
    need(canonical(actual) == canonical(expected),
         'exact certificate differs: wrong value, type, schema, or scope')


def references():
    for name, digest in PINS.items():
        need(hashlib.sha256(read(ROOT / files.safe_name(name))).hexdigest() == digest,
             'frozen reference modified: ' + name)
    return dict(PINS)


def frozen_terms(path, maximum):
    need(type(maximum) is int and maximum >= 0, 'invalid maximum index')
    text = read(path).decode('ascii')
    lines = text.splitlines(keepends=True)
    need(len(lines) == maximum + 1, 'wrong number of sequence rows')
    out = []
    for n, line in enumerate(lines):
        need(re.fullmatch(r'(0|[1-9][0-9]*) (0|[1-9][0-9]*)\n', line),
             'noncanonical sequence row at index ' + str(n))
        index, value = line[:-1].split(' ')
        need(index == str(n), 'wrong sequence index')
        out.append(int(value))
    return out


def derive():
    pins = references()
    original = load_certificate(ROOT / 'data/references/reference_hole_constants.json')
    result, coefficients, partitions = exact.derive(original)
    same(result, load_certificate(ROOT / 'data/references/exact_results.json'))
    need(coefficients == frozen_terms(ROOT / 'data/references/coefficients_0_5000.txt', 5000),
         'weighted coefficient vector differs')
    need(partitions == frozen_terms(ROOT / 'data/references/partitions_0_10000.txt', 10000),
         'ordinary partition vector differs')
    return {'schema_version': 1, 'report': 182, 'scope': dict(SCOPE),
            'exact_results': result, 'reference_sha256': pins}


def summary(value):
    result = value['exact_results']
    return {'status': 'PASS', 'report': 182,
            'certificate_sha256': hashlib.sha256(canonical(value)).hexdigest(),
            'weighted_coefficients_through': 5000, 'ordinary_partitions_through': 10000,
            'independent_recurrences_through': 600,
            'partitions_enumerated': result['ordinary_partitions_enumerated'],
            'low_hole_cases': result['low_hole_cases'],
            'low_hole_triples': result['low_hole_triples'],
            'scope': dict(SCOPE)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data', type=Path, default=ROOT / 'data/certificates.json')
    args = parser.parse_args()
    try:
        value = derive()
        same(value, load_certificate(args.data))
        print(canonical(summary(value)).decode(), end='')
    except (ValueError, RuntimeError, TypeError, KeyError, IndexError, OSError) as exc:
        print('VERIFICATION FAILED: ' + str(exc), file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())

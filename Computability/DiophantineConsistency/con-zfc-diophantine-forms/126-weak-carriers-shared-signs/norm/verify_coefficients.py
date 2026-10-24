#!/usr/bin/env python3
"""Replay the retained numeral recipe and compare all six delivered ports.

Standard library only.  The source recipe's main program requires normal
Python, so it is executed normally in a child even when this wrapper is run
with -O.  Its restriction and explicit checks remain intact.  The wrapper's
own checks use exceptions and remain active under optimization.

This is an authenticated recipe replay and exact byte comparison, not an
independent implementation or proof of the native compiler/refutation bridge.
No machine execution or search for a refutation is performed.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parent
COEFFICIENTS = ROOT / 'coefficients'
RECIPE = COEFFICIENTS / 'recipe'
SOURCE_PIN = '8c6eec9d19ef80538c8e61ff6e0180040583446a'
TUPLE = 'mixed-parity-unrounded-1064921'
PORT_MAP = {'beta': 'beta', 'K0': 'K', 'MC': 'MC', 'MF': 'MF_source'}
RECIPE_HASHES = {
    'source34_builder.py': 'bde405ebdb60dabd22590c4f7890d4373c62eb512d8bd084eff8affb17baa27a',
    'source34_binding.json': 'f15f1b10cb6a5912b1922ef34396b40453b4735e7a71dc36f230826370229afa',
    'k215.tm': 'fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090',
    'wang943_tiles.json': '66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f',
}
PORT_HASHES = {
    'beta': '6a029139964239dc65d716ccc186b40d9c5923ada0a4116cbb418d84534096ea',
    'K0': '18c40dd3b52b2882ee8346d098942ae487b54d0d040d9cd88f826b050794d1af',
    'MC': '3fc17cf73716c7528a91d45dc2bfffa8b76fb86d6d14f5451cf32c125a588777',
    'MF': '78a7befe6b09c6f59bb325aec1ef35caa72bc6a7d2d01fa39071b9c6e8d92722',
    'cone_A': '66463b4c98a7cd43faffe6cc0462f7f4fa65b7fd9bc57cba38789e585d59c615',
    'cone_B': '42be64ea01465eb227e9c993dba41affc2d9244aed8ec8f33d3268bda7c6b401',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def encode_unsigned(value):
    require(isinstance(value, int) and value > 0, 'nonpositive numeral')
    return value.to_bytes((value.bit_length()+7)//8, 'little')


def inspect_recipe():
    for name, expected_hash in RECIPE_HASHES.items():
        require(digest((RECIPE/name).read_bytes()) == expected_hash,
                'retained recipe/source hash mismatch: '+name)
    recorded = json.loads((RECIPE/'source34_binding.json').read_text())
    require(recorded['status'] == 'PASS' and recorded['source_pin'] == SOURCE_PIN,
            'source binding status/pin')
    require(recorded['variant'] == TUPLE and recorded['B'] == '2^1064921',
            'source tuple identity')
    require(recorded['ports'] == {'Bm1': 'beta', 'Kconstant': 'K',
                                  'MC': 'MC', 'MF': 'MF_source'},
            'recorded source port mapping')
    require(recorded['warning'] ==
            'Replace the complete tuple. MF is shifted MF_native+B-1.',
            'source shifted-MF convention')
    return recorded


def replay_recipe(recorded):
    """Run the unchanged checked main normally, keeping scratch bytes under norm."""
    # -E prevents an ambient PYTHONOPTIMIZE setting from accidentally disabling
    # normal execution. No -O flag is passed: the source __debug__ guard is run
    # unchanged and must succeed. Its explicit require checks also all execute.
    with tempfile.TemporaryDirectory(prefix='.coefficient-replay-', dir=ROOT) as temp:
        directory = Path(temp)
        command = [sys.executable, '-E', '-B', str(RECIPE/'source34_builder.py'),
                   '--output', str(directory)]
        run = subprocess.run(command, cwd=ROOT, capture_output=True, text=True,
                             timeout=60, check=False)
        require(run.returncode == 0,
                'normal source recipe failed: '+run.stderr[-4000:])
        regenerated = json.loads((directory/'COEFFICIENT_BINDING.json').read_text())
        require(json.loads(run.stdout) == regenerated,
                'source stdout/receipt disagreement')
        for field in ('status', 'source_pin', 'variant', 'B', 'ports', 'warning',
                      'ordinary_mathematical_adapter', 'new_kernel_certificate',
                      'audit', 'raw_bytes'):
            require(regenerated[field] == recorded[field],
                    'source recipe receipt mismatch: '+field)
        require(set(regenerated['payloads']) == set(PORT_MAP.values()),
                'regenerated port set')
        raws, details = {}, {}
        for target, source in PORT_MAP.items():
            raw = (directory/(source+'.bin')).read_bytes()
            reconstructed = gzip.decompress((directory/(source+'.bin.gz')).read_bytes())
            require(raw == reconstructed, 'source raw/gzip mismatch: '+source)
            value = int.from_bytes(raw, 'little')
            require(raw == encode_unsigned(value), 'source nonminimal encoding: '+source)
            actual_hash = digest(raw)
            old, new = recorded['payloads'][source], regenerated['payloads'][source]
            for entry in (old, new):
                require(entry['sha256'] == actual_hash == PORT_HASHES[target],
                        'source port hash mismatch: '+source)
                require(entry['bytes'] == len(raw) and entry['bits'] == value.bit_length(),
                        'source port size mismatch: '+source)
            raws[target] = raw
            # gzip container headers can differ across Python/zlib versions.
            # The exact integer and its minimal raw bytes are normative.
            details[target] = {
                'recipe_port': source, 'raw_bytes': len(raw), 'bits': value.bit_length(),
                'raw_sha256': actual_hash,
                'source_gzip_digest_matches_recorded': new['gzip_sha256'] == old['gzip_sha256'],
            }
        require(sum(len(v) for v in raws.values()) == recorded['raw_bytes'],
                'aggregate source raw size')
        return raws, details, regenerated['audit']


def compare_delivered_ports(raws, details):
    binding = json.loads((COEFFICIENTS/'BINDING.json').read_text())
    require(binding['tuple'] == TUPLE, 'delivered tuple identity')
    require(binding['source_commit'] == '2605669a532342f153b13eb6b4a0af4b54f5fa37',
            'delivered coefficient-binding source pin')
    require(binding['MF_convention'] == 'MF_native + beta, already shifted',
            'delivered shifted-MF convention')
    require(set(binding['payloads']) == set(PORT_HASHES), 'delivered port set')

    # The four recipe ports already include the source MF shift. In particular,
    # MF_source maps directly to MF: do not add beta a second time.
    beta = int.from_bytes(raws['beta'], 'little')
    shifted_mf = int.from_bytes(raws['MF'], 'little')
    require(beta == (1 << 1064921)-1, 'complete beta value')
    require(0 < shifted_mf-beta < beta, 'shifted MF/native range')
    for port, exponent in (('cone_A', 1113), ('cone_B', 666104)):
        raws[port] = encode_unsigned(1 << exponent)
        details[port] = {'recipe': '2**'+str(exponent), 'bits': exponent+1,
                         'raw_bytes': len(raws[port]), 'raw_sha256': digest(raws[port])}

    for port, rebuilt in raws.items():
        entry = binding['payloads'][port]
        require(entry['file'] == port+'.bin.gz', 'delivered port filename: '+port)
        require(entry['encoding'] == 'gzip of minimal unsigned little-endian bytes',
                'delivered numeral encoding: '+port)
        delivered = gzip.decompress((COEFFICIENTS/entry['file']).read_bytes())
        require(delivered == rebuilt, 'rebuilt/delivered bytes differ: '+port)
        integer = int.from_bytes(delivered, 'little')
        require(integer == int.from_bytes(rebuilt, 'little'),
                'rebuilt/delivered integer differs: '+port)
        require(delivered == encode_unsigned(integer), 'nonminimal delivered encoding: '+port)
        require(digest(delivered) == entry['raw_sha256'] == PORT_HASHES[port],
                'delivered binding/hash mismatch: '+port)
        require(len(delivered) == entry['raw_bytes'] and integer.bit_length() == entry['bits'],
                'delivered binding/size mismatch: '+port)
        if port.startswith('cone_'):
            require(entry['recipe'] == details[port]['recipe'], 'cone recipe binding: '+port)
        details[port]['delivered_integer_matches_recipe'] = True
        details[port]['delivered_minimal_bytes_match_recipe'] = True
        details[port]['recorded_binding_matches'] = True
    return details


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt', type=Path,
                        help='Optional receipt path within this norm directory; no default mutation.')
    args = parser.parse_args()
    if args.receipt:
        receipt = args.receipt.resolve()
        require(receipt.is_relative_to(ROOT), 'receipt must remain within norm directory')
    recorded = inspect_recipe()
    raws, details, source_audit = replay_recipe(recorded)
    details = compare_delivered_ports(raws, details)
    result = {
        'passed': True,
        'scope': 'authenticated source numeral-recipe replay and exact six-port integer/byte equality',
        'source_pin': SOURCE_PIN, 'tuple': TUPLE,
        'wrapper_optimization_level': sys.flags.optimize,
        'source_recipe_execution': 'normal Python; unchanged main guard and all checks active',
        'optimized_limitation': 'The retained recipe main forbids -O; optimized wrapper runs it in a normal child.',
        'port_mapping': PORT_MAP,
        'MF_convention': 'MF_source is already shifted; copied to MF without another addition',
        'authenticated_recipe_files': RECIPE_HASHES,
        'source_audit': source_audit, 'ports': details,
        'machine_simulated': False, 'unbounded_calibration_reproved': False,
        'temporary_recipe_outputs_removed': True,
    }
    text = json.dumps(result, indent=2)+'\n'
    if args.receipt:
        receipt.parent.mkdir(parents=True, exist_ok=True)
        receipt.write_text(text)
    print(text)


if __name__ == '__main__':
    main()

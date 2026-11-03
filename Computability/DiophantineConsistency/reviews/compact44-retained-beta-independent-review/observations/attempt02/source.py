#!/usr/bin/env python3
"""Independent arithmetic/payload and recorded-build inspection, not a Lean replay."""
from hashlib import sha256
from pathlib import Path
import gzip
import json
import sys

ROOT = Path(__file__).resolve().parents[4]
BASE = ROOT / 'Computability/DiophantineConsistency'
PROTOTYPE = BASE / 'research/ordinary12-ipra-bridge/compact44-retained-beta-byte-prototype'
FROZEN = BASE / 'research/ordinary12-ipra-bridge/compact44-fixed-graph-digits-prototype'
PARENT = BASE / 'candidates/free-j-polarized-positive/source/positive/coefficients'
SUPPLEMENT = BASE / 'con-zfc-diophantine-forms/115-synchronized-exponents/supplement'
INPUTS = {
    'lean_source': (PROTOTYPE / 'RetainedBetaBytes.lean', '843341bb3fde311235b893a35245c3cbc7d7ae5c869fefd6aece51262b26757c'),
    'frozen_beta_source': (FROZEN / 'observations/attempt01/CompactFixedBeta.lean', '9adc356351adfdeb2ccfcfe61cbf18fcd8a8458c911fabd91d07fe49ce85fcd5'),
    'external_checker': (PROTOTYPE / 'check_payload.py', 'd9f45198470682bb4925bc458ad9fa3ec488a8dffc9d5e8ad9f6f912e08a492b'),
    'author_receipt': (PROTOTYPE / 'observations/attempt03/terminal.json', 'a3dc3b7b2db27d2d5c54e297c62096ff027487b2a68ec890ad001d371b081189'),
    'author_log': (PROTOTYPE / 'observations/attempt03/compile.log', '25aa948864c1f84ad0da945aaa06ca861c583098876bccbc2c05f857cd8a2c58'),
    'parent_binding': (PARENT / 'BINDING.json', 'dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'),
    'parent_gzip': (PARENT / 'payloads/beta.bin.gz', '466796f146d60db9929fa0f0f62d70d5e6afbcea9940342764571f1ca6bea87c'),
    'graph_json': (SUPPLEMENT / 'circuits/positive12_95_degree70.json', '2348183cb8e366433f668cdcc9d77ca9c7e2d0c55b7b630bda39bd8db7506d22'),
    'author_object': (Path('/tmp/compact44-retained-beta-byte-author-ap_xzsq2/RetainedBetaBytes.olean'), 'bd1611b2a0a3343d204c558628514b0e7132921a4263429c27b1f296ee03585b'),
    'beta_object': (Path('/tmp/ipra-compact-fixed-graph-digits-pair-01/author/lib/DiophantineConsistency/CompactFixedBeta.olean'), 'a5d7c2f783e2c1bb527147e883f3433ae389079dd85562ab7aba047990f7cb02'),
}

def digest(b):
    return sha256(b).hexdigest()

before = {name: path.read_bytes() for name, (path, _) in INPUTS.items()}
if any(digest(before[name]) != pin for name, (_, pin) in INPUTS.items()):
    raise RuntimeError('input pin mismatch')
binding = json.loads(before['parent_binding'])['ports']['beta']
graph = json.loads(before['graph_json'])
receipt = json.loads(before['author_receipt'])
data = gzip.decompress(before['parent_gzip'])
bits = 67 * 8807
value = int.from_bytes(data, byteorder='little', signed=False)
length, remaining = divmod(bits, 8)
checks = {
    'bits': bits,
    'full_bytes': length,
    'remaining_bits': remaining,
    'raw_length': len(data),
    'raw_sha256': digest(data),
    'raw_hash_matches_expected': digest(data) == '0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d',
    'value_is_two_power_minus_one': value == (1 << bits) - 1,
    'byte_values_exact': len(data) == length + 1 and all(b == 255 for b in data[:length]) and data[-1] == (1 << remaining) - 1,
    'minimal_byte_count': len(data) == (value.bit_length() + 7) // 8,
    'binding_bits_match': binding['bits'] == bits,
    'binding_length_matches': binding['raw_bytes'] == len(data),
    'binding_raw_hash_matches': binding['sha256_raw'] == digest(data),
    'binding_gzip_hash_matches': binding['sha256_gzip'] == digest(before['parent_gzip']),
    'graph_port_order': graph['fixed_numerals'],
    'graph_beta_is_first_port': graph['fixed_numerals'] == ['beta', 'K0', 'MC', 'MF'],
    'graph_binding_reference': graph['coefficient_binding'],
    'author_exit_zero': receipt['exit_code'] == 0,
    'author_guards_unchanged': receipt['guards_unchanged'],
    'author_source_hash_matches': receipt['source_sha256'] == digest(before['lean_source']),
    'author_object_hash_matches': receipt['object_sha256'] == digest(before['author_object']),
    'author_log_clean': all(word not in before['author_log'].decode() for word in ('error:', 'warning:', 'sorryAx')),
    'frozen_beta_def_matches': b'def betaNat : \xe2\x84\x95 := 2^(67*8807)-1' in before['frozen_beta_source'],
}
after = {name: path.read_bytes() for name, (path, _) in INPUTS.items()}
checks['inputs_unchanged'] = before == after
flags = [v for v in checks.values() if isinstance(v, bool)]
if not all(flags):
    print(json.dumps(checks, indent=2, sort_keys=True))
    sys.exit(1)
print(json.dumps(checks, indent=2, sort_keys=True))

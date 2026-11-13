#!/usr/bin/env python3
"""External sparse-MC transcription and retained parent payload comparison."""
from hashlib import sha256
from pathlib import Path
import gzip
import json

root = Path(__file__).resolve().parents[4]
base = root / 'Computability/DiophantineConsistency'
parent = base / 'candidates/free-j-polarized-positive/source/positive/coefficients'
binding_path = parent / 'BINDING.json'
payload_path = parent / 'payloads/MC.bin.gz'
binding = binding_path.read_bytes()
compressed = payload_path.read_bytes()
meta = json.loads(binding)['ports']['MC']
support = (set(range(943)) | set(range(983, 993)) | set(range(1003, 1012)) |
           set(range(1013, 1032)) | {1063, 1064, 1095, 2195, 3296}) - {1}
sparse_value = ((1 << 590069) - 1 - sum(1 << (67*j) for j in support)
                - 2*(1 << (67*1063)))
recipe = sparse_value.to_bytes((sparse_value.bit_length()+7)//8, 'little')
raw = gzip.decompress(compressed)
h = lambda b: sha256(b).hexdigest()
checks = {
    'binding_pin': h(binding) == 'dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01',
    'binding_unchanged': binding_path.read_bytes() == binding,
    'gzip_pin': h(compressed) == '271fabccdd555bda2c54c4c3a7379cc02eeba4893c07178bfd557a7683b74d5e',
    'gzip_matches_binding': h(compressed) == meta['sha256_gzip'],
    'gzip_unchanged': payload_path.read_bytes() == compressed,
    'raw_sha256': h(raw),
    'raw_pin': h(raw) == '6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4',
    'raw_matches_binding': h(raw) == meta['sha256_raw'],
    'byte_count': len(raw),
    'bit_count': sparse_value.bit_length(),
    'length_matches_binding': len(raw) == meta['raw_bytes'],
    'bits_match_binding': sparse_value.bit_length() == meta['bits'],
    'minimal_length': len(raw) == (sparse_value.bit_length()+7)//8,
    'support_count': len(support),
    'support_count_matches': len(support) == 985,
    'special_is_supported': 1063 in support,
    'forbidden_selector_removed': 1 not in support,
    'raw_equals_sparse_recipe': raw == recipe,
}
print(json.dumps(checks, sort_keys=True, indent=2))
if not all(v for v in checks.values() if isinstance(v, bool)):
    raise SystemExit(1)

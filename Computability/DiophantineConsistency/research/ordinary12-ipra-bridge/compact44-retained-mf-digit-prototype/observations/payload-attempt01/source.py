#!/usr/bin/env python3
"""Externally compare the once-shifted high-digit recipe to parent MF gzip."""
from hashlib import sha256
from pathlib import Path
import gzip
import json

root=Path(__file__).resolve().parents[5]
base=root/'Computability/DiophantineConsistency'
parent=base/'candidates/free-j-polarized-positive/source/positive/coefficients'
binding_path=parent/'BINDING.json'
payload_path=parent/'payloads/MF_source.bin.gz'
high_path=base/'research/ordinary12-ipra-bridge/compact44-high-population-prototype/CompactHighPopulation.lean'
binding=binding_path.read_bytes(); compressed=payload_path.read_bytes(); high_source=high_path.read_bytes()
meta=json.loads(binding)['ports']['MF']
high_digits=([4]+[0]*1012+[1]*10+[0]*42+[1]*9+[0]*1121+[1]+[0]*1100+[1]+
             [0]*1096+[(1<<51)-2]+[0]*1101+[(1<<51)-2]+[0]*3296+
             [(1<<65)-1]*13+[(1<<19)-1,0])
high=sum(d<<(67*i) for i,d in enumerate(high_digits))
beta=(1<<590069)-1
once_shifted=beta+high
shifted_digits=[3]+high_digits[1:]+[1]
by_digits=sum(d<<(67*i) for i,d in enumerate(shifted_digits))
raw=gzip.decompress(compressed)
expected=once_shifted.to_bytes((once_shifted.bit_length()+7)//8,'little')
h=lambda b:sha256(b).hexdigest()
checks={
  'binding_pin':h(binding)=='dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01',
  'binding_unchanged':binding_path.read_bytes()==binding,
  'high_source_pin':h(high_source)=='b1e962aed2f9fc2b49533a52f3508a84af4d433c4a9fae210540e085056dab1d',
  'high_source_unchanged':high_path.read_bytes()==high_source,
  'gzip_pin':h(compressed)=='935cd87f8b23f24a20fd742c48d2a9cbca6afd494b6b074445df72c98b0c6e3b',
  'gzip_matches_binding':h(compressed)==meta['sha256_gzip'],
  'gzip_unchanged':payload_path.read_bytes()==compressed,
  'raw_pin':h(raw)=='48333b0d30a4edeb8579f44286cb59806c5622cb42b367f5b5f9ee827711c737',
  'raw_matches_binding':h(raw)==meta['sha256_raw'],
  'original_digit_count':len(high_digits),
  'original_digit_count_matches':len(high_digits)==8807,
  'original_low_digit_is_four':high_digits[0]==4,
  'shifted_digit_count':len(shifted_digits),
  'shifted_digits_bounded':all(0<=d<1<<67 for d in shifted_digits),
  'once_shifted_matches_digit_transformation':once_shifted==by_digits,
  'bytes_equal_once_shifted':raw==expected,
  'raw_length':len(raw),'length_matches_binding':len(raw)==meta['raw_bytes'],
  'bit_length':once_shifted.bit_length(),'bits_match_binding':once_shifted.bit_length()==meta['bits'],
  'minimal_length':len(raw)==(once_shifted.bit_length()+7)//8,
}
print(json.dumps(checks,indent=2,sort_keys=True))
if not all(v for v in checks.values() if isinstance(v,bool)): raise SystemExit(1)

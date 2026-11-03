#!/usr/bin/env python3
"""Externally compare the MF local-window byte recipe to retained parent data."""
from hashlib import sha256
from pathlib import Path
import gzip
import json

root=Path(__file__).resolve().parents[5]
base=root/'Computability/DiophantineConsistency'
parent=base/'candidates/free-j-polarized-positive/source/positive/coefficients'
binding_path=parent/'BINDING.json'; payload_path=parent/'payloads/MF_source.bin.gz'
high_path=base/'research/ordinary12-ipra-bridge/compact44-high-population-prototype/CompactHighPopulation.lean'
window_path=base/'research/ordinary12-ipra-bridge/compact44-mf-byte-window-prototype/CompactShiftedHighByteWindow.lean'
binding=binding_path.read_bytes(); compressed=payload_path.read_bytes()
high_source=high_path.read_bytes(); window_source=window_path.read_bytes()
meta=json.loads(binding)['ports']['MF']
high=([4]+[0]*1012+[1]*10+[0]*42+[1]*9+[0]*1121+[1]+[0]*1100+[1]+
      [0]*1096+[(1<<51)-2]+[0]*1101+[(1<<51)-2]+[0]*3296+
      [(1<<65)-1]*13+[(1<<19)-1,0])
shifted=[3]+high[1:]+[1]
def digit(i): return shifted[i] if i<len(shifted) else 0
def byte_at(j):
    i,r=divmod(8*j,67)
    return ((digit(i)>>r)+(digit(i+1)<<(67-r))) % 256
recipe=bytes(byte_at(j) for j in range(73759))
raw=gzip.decompress(compressed)
h=lambda b:sha256(b).hexdigest()
checks={
  'binding_pin':h(binding)=='dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01',
  'binding_unchanged':binding_path.read_bytes()==binding,
  'high_source_pin':h(high_source)=='b1e962aed2f9fc2b49533a52f3508a84af4d433c4a9fae210540e085056dab1d',
  'high_source_unchanged':high_path.read_bytes()==high_source,
  'window_source_pin':h(window_source)=='851c763f5b6e4ea48ffea96fba6d03e71e676a83bfe6857e37b4b254c0c5f082',
  'window_source_unchanged':window_path.read_bytes()==window_source,
  'gzip_pin':h(compressed)=='935cd87f8b23f24a20fd742c48d2a9cbca6afd494b6b074445df72c98b0c6e3b',
  'gzip_matches_binding':h(compressed)==meta['sha256_gzip'],
  'payload_unchanged':payload_path.read_bytes()==compressed,
  'raw_pin':h(raw)=='48333b0d30a4edeb8579f44286cb59806c5622cb42b367f5b5f9ee827711c737',
  'raw_matches_binding':h(raw)==meta['sha256_raw'],
  'high_digit_count':len(high), 'shifted_digit_count':len(shifted),
  'length_matches_binding':len(raw)==meta['raw_bytes']==len(recipe),
  'all_recipe_bytes_match':recipe==raw,
  'recipe_sha256':h(recipe), 'raw_sha256':h(raw),
}
print(json.dumps(checks,indent=2,sort_keys=True))
if not all(v for v in checks.values() if isinstance(v,bool)): raise SystemExit(1)

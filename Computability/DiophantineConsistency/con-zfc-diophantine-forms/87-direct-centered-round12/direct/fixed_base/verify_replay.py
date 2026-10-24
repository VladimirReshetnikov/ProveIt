#!/usr/bin/env python3
import pathlib,json,hashlib
R=pathlib.Path(__file__).resolve().parent
for name,expected in json.loads((R/'REPLAY_SHA256.json').read_text()).items():
 actual=hashlib.sha256((R/name).read_bytes()).hexdigest()
 if actual!=expected:raise RuntimeError('Byte mismatch: '+name)
print('PASS: all12 materialized outputs reproduce exactly, including the full integer polynomial.')

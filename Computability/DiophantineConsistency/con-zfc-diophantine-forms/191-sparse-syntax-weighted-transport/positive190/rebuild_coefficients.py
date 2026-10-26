#!/usr/bin/env python3
"""Replay the frozen finite numeral recipe without changing any output file."""
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent
source=ROOT/'inherited/rebuild_coefficients_parent.py'
spec=importlib.util.spec_from_file_location('frozen_numeral_recipe',source)
module=importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
graph=json.loads((ROOT/'equation.json').read_text())
receipts=[]
for name,value in module.reconstruct().items():
    meta=graph['coefficient_binding']['ports'][name]
    raw=value.to_bytes((value.bit_length()+7)//8,'little')
    if hashlib.sha256(raw).hexdigest()!=meta['raw_sha256']:
        raise ValueError('Reconstructed numeral hash mismatch: '+name)
    if raw!=gzip.decompress((ROOT/'coefficients'/meta['file']).read_bytes()):
        raise ValueError('Reconstructed numeral payload mismatch: '+name)
    receipts.append({'port':name,'bits':value.bit_length(),'raw_sha256':meta['raw_sha256']})
print(json.dumps({'status':'passed','finite_recipe_characters':len(module.CODE),'ports':receipts},indent=2))

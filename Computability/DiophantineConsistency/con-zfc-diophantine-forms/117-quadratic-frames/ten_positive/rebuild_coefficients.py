#!/usr/bin/env python3
"""Reconstruct all four fixed integers from the closed printed recipe."""
from pathlib import Path
import json,gzip,hashlib,importlib.util
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('pinned_coefficient_recipe',HERE/'upstream/coefficient_constructor.py')
recipe=importlib.util.module_from_spec(spec);spec.loader.exec_module(recipe)
seed=(HERE/'SEED.txt').read_text().strip()
ports,tiles,audit=recipe.construct(recipe.decode(seed))
binding=json.loads((HERE/'coefficients/BINDING.json').read_text());out=[]
for n,p in binding['ports'].items():
    value=ports[{'K0':'K','MF':'MF_source'}.get(n,n)]
    raw=value.to_bytes((value.bit_length()+7)//8,'little')
    if raw!=gzip.decompress((HERE/'coefficients'/p['file']).read_bytes()):raise ValueError('complete printed coefficient mismatch '+n)
    out.append({'port':n,'bits':value.bit_length(),'raw_sha256':hashlib.sha256(raw).hexdigest()})
result={'status':'PASS','seed_characters':len(seed),'distinct_tiles':len(tiles),'ports':out,'finite_native_checks':audit,
        'scope':'Closed coefficient recipe and finite native premises, not an end-to-end formal semantic proof.'}
(HERE/'COEFFICIENT_CHECK.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

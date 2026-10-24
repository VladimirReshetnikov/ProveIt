#!/usr/bin/env python3
"""Reconstruct every fixed coefficient from the reviewed finite source34 recipe."""
from pathlib import Path
import importlib.util,gzip,json,hashlib
ROOT=Path(__file__).resolve().parent
p=ROOT/'coefficients/recipe/source34_builder.py'
spec=importlib.util.spec_from_file_location('reviewed_source34_recipe',p)
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
ports,audit=m.construct()
ports={'beta':ports['beta'],'K0':ports['K'],'MC':ports['MC'],'MF':ports['MF_source'],'cone_A':2**1113,'cone_B':2**666104}
binding=json.loads((ROOT/'coefficients/BINDING.json').read_text());rows={}
for name,v in ports.items():
    row=binding['payloads'][name];raw=gzip.decompress((ROOT/'coefficients'/row['file']).read_bytes())
    if int.from_bytes(raw,'little')!=v:raise ValueError(name+' payload differs from recipe')
    if hashlib.sha256(raw).hexdigest()!=row['raw_sha256']:raise ValueError(name+' digest')
    rows[name]={'bits':v.bit_length(),'raw_sha256':hashlib.sha256(raw).hexdigest(),'recipe_exact_match':True}
print(json.dumps({'status':'PASS','payloads':rows,'source34_basis_checks':audit},indent=2))

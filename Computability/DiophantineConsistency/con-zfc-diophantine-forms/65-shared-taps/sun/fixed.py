#!/usr/bin/env python3
"""Authenticated complete fixed-port binding and exact/modular leaf values."""
from pathlib import Path
import gzip,hashlib,json
R=Path(__file__).resolve().parent

def ports():
    binding=json.loads((R/'coefficients/COEFFICIENT_BINDING.json').read_text())
    values=[]
    for rec in binding['files']:
        path=R/'coefficients'/rec['file'];compressed=path.read_bytes();raw=gzip.decompress(compressed)
        if hashlib.sha256(compressed).hexdigest()!=rec['gzip_sha256']:raise ValueError('compressed coefficient hash')
        if hashlib.sha256(raw).hexdigest()!=rec['sha256']:raise ValueError('raw coefficient hash')
        value=int.from_bytes(raw,'little')
        if value.bit_length()!=rec['bit_length']:raise ValueError('coefficient bit length')
        values.append(value)
    if [x['port'] for x in binding['files']]!=['beta','K','MC','MF_source']:raise ValueError('coefficient order')
    return values

def leaves(body,modulus=None):
    pp=ports();out={}
    for name,recipe in body['coefficient_recipes'].items():
        value=0
        for rec in recipe:
            term=rec['coefficient']
            for p,e in zip(pp,rec['powers']):term*=p**e if modulus is None else pow(p,e,modulus)
            value+=term
        out[name]=value if modulus is None else value%modulus
    for name,key in [('beta_source','base_scale_exponent'),('beta_mask','mask_scale_exponent')]:
        out[name]=(1<<body[key]) if modulus is None else pow(2,body[key],modulus)
    return out

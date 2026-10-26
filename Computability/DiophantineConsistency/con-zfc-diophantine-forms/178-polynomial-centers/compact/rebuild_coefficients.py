#!/usr/bin/env python3
"""Reconstruct the complete fixed tuple using the retained finite recipe.

The source recipe is copied byte-for-byte from the pinned parent. This
wrapper adapts only its path interface to this package. No simulation,
consistency assumption, or search for a root is performed.
"""
from pathlib import Path
import gzip
import hashlib
import importlib.util
import json

ROOT=Path(__file__).resolve().parent


def main():
    spec=importlib.util.spec_from_file_location('retained_coefficient_recipe',
                                              ROOT/'parents/rebuild_coefficients_source.py')
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    values=module.reconstruct()
    binding=json.loads((ROOT/'equations/centered_transport88.json').read_text())['coefficient_binding']
    receipt=[]
    for name,meta in binding['ports'].items():
        value=values[name]
        raw=value.to_bytes((value.bit_length()+7)//8,'little')
        if hashlib.sha256(raw).hexdigest()!=meta['raw_sha256']:
            raise ValueError('recipe hash mismatch: '+name)
        if value.bit_length()!=meta['bits']:
            raise ValueError('recipe bit length: '+name)
        data=(ROOT/binding['path']/meta['file']).read_bytes()
        if gzip.decompress(data)!=raw:
            raise ValueError('payload differs from reconstructed integer: '+name)
        receipt.append({'port':name,'bits':value.bit_length(),
                        'raw_sha256':meta['raw_sha256']})
    print(json.dumps({'whole_tuple_reconstructed':True,'ports':receipt},indent=2))


if __name__=='__main__':main()

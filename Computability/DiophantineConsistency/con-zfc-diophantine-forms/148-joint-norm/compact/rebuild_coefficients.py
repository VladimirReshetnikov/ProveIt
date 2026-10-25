#!/usr/bin/env python3
"""Reconstruct the unchanged whole four-integer tuple from its finite seed."""
from pathlib import Path
import gzip
import hashlib
import json
import runpy

ROOT=Path(__file__).resolve().parent

def check():
    recipe=runpy.run_path(str(ROOT/'inherited/rebuild_coefficients.py'))['reconstruct']
    values=recipe()
    binding=json.loads((ROOT/'equation78_degree454.json').read_text())['coefficient_binding']['ports']
    report=[]
    for name,value in values.items():
        b=binding[name]
        raw=value.to_bytes((value.bit_length()+7)//8,'little')
        if value.bit_length()!=b['bits'] or hashlib.sha256(raw).hexdigest()!=b['raw_sha256']:
            raise ValueError('Reconstructed tuple differs: '+name)
        if gzip.decompress((ROOT/'coefficients'/b['file']).read_bytes())!=raw:
            raise ValueError('Literal tuple payload differs: '+name)
        report.append({'port':name,'bits':b['bits'],'raw_sha256':b['raw_sha256']})
    return report

if __name__=='__main__':print(json.dumps(check(),indent=2))

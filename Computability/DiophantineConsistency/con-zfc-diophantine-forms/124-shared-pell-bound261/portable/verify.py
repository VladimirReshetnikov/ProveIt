#!/usr/bin/env python3
"""Independent exact natural-domain elimination and polynomial verification.

This entry point imports the independent inherited checker, never a builder.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json

HERE=Path(__file__).resolve().parent

def main():
    p=argparse.ArgumentParser();p.add_argument('--variant',choices=['primary','sparse','both'],default='both')
    a=p.parse_args()
    source_map=json.loads((HERE/'SOURCE_MAP.json').read_text())
    for item in source_map['files']:
        actual=hashlib.sha256((HERE/item['path']).read_bytes()).hexdigest()
        if actual!=item['sha256']:raise ValueError('Source map hash mismatch: '+item['path'])
    checker_path=next(HERE/x['path'] for x in source_map['files'] if x['path'].endswith('/psd_contract/check.py'))
    spec=importlib.util.spec_from_file_location('independent_contraction_checker',checker_path)
    check=importlib.util.module_from_spec(spec);spec.loader.exec_module(check)
    receipts=[]
    for variant in (['primary','sparse'] if a.variant=='both' else [a.variant]):
        base=HERE/'equations'/variant
        source=json.loads((base/'raw/equation.json').read_text())
        target=json.loads((base/'natural/equation.json').read_text())
        cert=json.loads((base/'natural/elimination_certificate.json').read_text())
        expanded=json.loads((base/'natural/expanded_polynomial.json').read_text())
        receipt,terms=check.verify(source,target,cert)
        if terms!=expanded['terms']:raise ValueError('Expanded coefficient mismatch: '+variant)
        receipts.append({'variant':variant,**receipt})
    print(json.dumps({'source_hashes_verified':len(source_map['files']),
                      'producer_modules_imported':False,'receipts':receipts},indent=2))

if __name__=='__main__':main()

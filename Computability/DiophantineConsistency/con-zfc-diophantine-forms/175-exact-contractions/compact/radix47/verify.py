#!/usr/bin/env python3
"""Check the whole47 specialization, using free-polynomial checker arithmetic.

Imports no producer. Every coefficient port is checked against the entire
retained native P66 tuple; the two new gate lists must match their already
proved generic companions exactly.
"""
import argparse, hashlib, importlib.util, json, sys
from pathlib import Path

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent))


def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    obj=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(obj)
    return obj


def run():
    pins=json.loads((ROOT/'SOURCE_LEDGER.json').read_text())
    for item in pins['sources']:
        if hashlib.sha256((ROOT/item['local']).read_bytes()).hexdigest()!=item['sha256']:
            raise ValueError('Retained source identity differs: '+item['local'])
    original_native_pins={
        'phi_coefficients.json':'876ace3f98030b035d392d14cdb6003fb612ec0d18db33ca234b8164856cc9d3',
        'native_geometry.json':'e4f37db7afd2aa5fe8b1b20c5394f12d90cf28527fa9b68754672d5a0725a0ba',
        'polynomial.json':'174057a94e7f440a5caba35e30e4d8ea1713cefb6b6541f3102342ee1260839d',
        'radix47_proof.md':'3c854e9fb951f030f9d5b9dc7186c3be98f65cf4b94c63810869add08ec2c224'}
    for name,digest in original_native_pins.items():
        path=ROOT/'inherited/provenance/radix47/radix47'/name
        if hashlib.sha256(path.read_bytes()).hexdigest()!=digest:
            raise ValueError('Original native bridge source pin differs: '+name)
    checker=module('free_port_exact_checker',ROOT.parent/'verify.py')
    checker.ROOT=ROOT
    recipe=module('whole47_fixed_recipe',ROOT/'inherited/rebuild_coefficients_149.py')
    actual=recipe.reconstruct()
    native=json.loads((ROOT/'inherited/provenance/radix47/radix47/polynomial.json').read_text())
    native=native['coefficient_binding']['ports']
    old=json.loads((ROOT/'inherited/inverse_bV164.json').read_text())['coefficient_binding']['ports']
    for name,meta in old.items():
        for key in ('raw_sha256','gzip_sha256','bits'):
            checker.require(meta[key]==native[name][key],'inherited native binding '+name)
        raw=actual[name].to_bytes((actual[name].bit_length()+7)//8,'little')
        checker.require(hashlib.sha256(raw).hexdigest()==meta['raw_sha256'],'finite recipe '+name)
    proof=ROOT/'inherited/provenance/radix47/radix47/radix47_proof.md'
    checker.require(hashlib.sha256(proof.read_bytes()).hexdigest()=='3c854e9fb951f030f9d5b9dc7186c3be98f65cf4b94c63810869add08ec2c224','native bridge proof identity')
    results=[]
    for path in sorted((ROOT/'equations').glob('*.json')):
        graph=json.loads(path.read_text())
        parent_path=ROOT/graph['parent']['path']
        parent=json.loads(parent_path.read_text())
        checker.require(hashlib.sha256(parent_path.read_bytes()).hexdigest()==graph['parent']['sha256'],'free-port parent identity')
        checker.require(graph['source']==parent['source'],'free-port rows changed')
        checker.require(graph['coefficient_binding']['ports']==old,'ports were mixed or changed')
        results.append({'file':str(path.relative_to(ROOT)),
            'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
            'operations':checker.topology(graph),'cuts':checker.cuts(graph),
            'leading':checker.leading(graph),'coefficients':checker.coefficient_binding(graph),
            'corruptions_rejected':checker.mutation_controls(graph)})
    return {'whole_tuple':'complemented-label radix47, source MF shifted once',
            'raw_bytes':sum((x.bit_length()+7)//8 for x in actual.values()),
            'largest_port_bits':max(x.bit_length() for x in actual.values()),
            'native_target_identities_checked':51,'phi_coefficients_checked':3297,
            'circuits':results}


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--receipt',type=Path)
    args=parser.parse_args()
    result=run()
    if args.receipt:args.receipt.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'raw_bytes':result['raw_bytes'],'largest_port_bits':result['largest_port_bits'],
         'circuits':[{'file':x['file'],'operations':sum(x['operations'].values()),
                      'degree':x['leading']['degree'],'cuts':len(x['cuts']),
                      'corruptions_rejected':x['corruptions_rejected']}
                     for x in result['circuits']]},indent=2))

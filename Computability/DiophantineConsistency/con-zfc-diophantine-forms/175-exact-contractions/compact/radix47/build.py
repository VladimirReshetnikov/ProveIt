#!/usr/bin/env python3
"""Specialize both new graphs to one complete calibrated radix47 tuple.

The native proof and coefficient improvement are inherited. This script
changes all four fixed ports together, without altering any free-port gate.
"""
import argparse, copy, gzip, hashlib, importlib.util, json
from pathlib import Path

ROOT=Path(__file__).resolve().parent


def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    obj=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(obj)
    return obj


def construct(weight):
    parent=ROOT.parent/'equations'/('inverse_trace85_degree232_'+weight+'.json')
    graph=json.loads(parent.read_text())
    reference=json.loads((ROOT/'inherited/inverse_bV164.json').read_text())
    graph['coefficient_binding']=copy.deepcopy(reference['coefficient_binding'])
    graph['coefficient_binding']['path']='coefficients/'
    graph.update(name='whole47_inverse_trace85_degree232_'+weight,
        parent={'path':'../equations/'+parent.name,
                'sha256':hashlib.sha256(parent.read_bytes()).hexdigest()},
        specialization='Complete complemented-label radix47 tuple; inherited '
                       'native controller and carry proof; never mixed ports.',
        proof='PROOF.md')
    return graph


def run(check=False):
    reference=construct('b2')['coefficient_binding']['ports']
    native=json.loads((ROOT/'inherited/provenance/radix47/radix47/polynomial.json').read_text())
    for name,meta in reference.items():
        for key in ('raw_sha256','gzip_sha256','bits'):
            if meta[key]!=native['coefficient_binding']['ports'][name][key]:
                raise ValueError('Whole native P66 binding mismatch: '+name)
    proof=ROOT/'inherited/provenance/radix47/radix47/radix47_proof.md'
    if hashlib.sha256(proof.read_bytes()).hexdigest()!='3c854e9fb951f030f9d5b9dc7186c3be98f65cf4b94c63810869add08ec2c224':
        raise ValueError('Native proof is not the one identified by the bridge')
    recipe=module('retained_whole47_recipe',ROOT/'inherited/rebuild_coefficients_149.py')
    values=recipe.reconstruct()
    # reconstruct() also checks all3297 coefficients, all51 target identities,
    # native mask populations/phases, carry premises, actual controller primes,
    # exact orders and the valuation-one lift for the complete new integer K0.
    receipt=[]
    for name,value in values.items():
        meta=reference[name]
        raw=value.to_bytes((value.bit_length()+7)//8,'little')
        if hashlib.sha256(raw).hexdigest()!=meta['raw_sha256'] or value.bit_length()!=meta['bits']:
            raise ValueError('Reconstructed coefficient mismatch: '+name)
        path=ROOT/'coefficients'/meta['file']
        if not check:
            path.write_bytes(gzip.compress(raw,compresslevel=9,mtime=0))
        if gzip.decompress(path.read_bytes())!=raw:
            raise ValueError('Coefficient payload mismatch: '+name)
        if hashlib.sha256(path.read_bytes()).hexdigest()!=meta['gzip_sha256']:
            raise ValueError('Compressed coefficient identity differs: '+name)
        receipt.append({'port':name,'bits':value.bit_length(),
                        'raw_bytes':len(raw),'raw_sha256':meta['raw_sha256']})
    for weight in ('b2','bV'):
        graph=construct(weight)
        text=json.dumps(graph,indent=2)+'\n'
        path=ROOT/'equations'/(graph['name']+'.json')
        if check:
            if path.read_text()!=text:raise ValueError('Graph reconstruction mismatch')
        else:path.write_text(text)
    result={'coefficients':receipt,'raw_bytes':sum(x['raw_bytes'] for x in receipt),
            'largest_port_bits':max(x['bits'] for x in receipt),
            'phi_coefficients_checked':3297,'native_target_identities_checked':51,
            'native_proof_sha256':hashlib.sha256(proof.read_bytes()).hexdigest()}
    if not check:(ROOT/'BUILD.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--check',action='store_true')
    run(parser.parse_args().check)

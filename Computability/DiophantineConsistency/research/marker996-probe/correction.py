#!/usr/bin/env python3
"""Reconstruct the entire physical label map and refute the frozen996 phase premise."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
PARENT=HERE.parent/'padding-staircase-independent/certify.py'
PARENT_SHA='56b3865237699c486bbd940a88e94387d26092ac2cf89cd7f9097206dd8fb975'
FROZEN_SHA='dea15e895186d44c00af1946938dd399b4df52da449a2f9e83c9179a0d2d9499'


def require(test,message):
    if not test: raise ValueError(message)


def sha(data):return hashlib.sha256(data).hexdigest()


def encoded(data):return (json.dumps(data,indent=2,sort_keys=True)+'\n').encode()


def run():
    require(sha(PARENT.read_bytes())==PARENT_SHA,'Exact complete reviewed2011 source')
    require(sha((HERE/'probe.py').read_bytes())==FROZEN_SHA,'Original failed semantic probe preserved byte-exact')
    spec=importlib.util.spec_from_file_location('reviewed2011_label_map',PARENT)
    require(spec is not None and spec.loader is not None,'Authenticated loader')
    parent=importlib.util.module_from_spec(spec);spec.loader.exec_module(parent)
    _,_,seed,actions,tiles,c,support=parent.source()
    labels=sorted(e for e in support if e>=942 and c[e])
    require(len(labels)==34,'Every physical weighted label field')
    mapping={}
    for e in labels:
        require(c[e]%2048==0,'Integral count-normalized label coefficient')
        weight=c[e]//2048
        require(weight>0 and weight&(weight-1)==0,'Every label weight is one exact power of two')
        mapping[e]=weight.bit_length()-1
    require(sorted(mapping.values())==list(range(34)),'Full bijection from physical fields to all34 packed bits')
    rows=[]
    for j,(w,n,e,s) in enumerate(tiles):
        packed=(255-w)+((511-n)<<8)+((255-e)<<17)+((511-s)<<25)
        bits={field:(packed>>index)&1 for field,index in mapping.items()}
        require(sum((c[field]//2048)*bit for field,bit in bits.items())==packed,
                'Entire actual physical label word equals the decoded packed complement')
        require(c[j]+sum(c[field]*bit for field,bit in bits.items())==(1<<45)+2,
                'Whole selector and all34 labels exactly satisfy the canonical count clause')
        rows.append([j,packed,[[field,bits[field]] for field in labels]])
    actual=dict(rows[0][2])
    require(mapping[978]==0 and mapping[979]==1 and mapping[969]==17,
            'Physical978 block is packedWest; physical969 block is packedEast')
    require(tuple(tiles[0])==(2,435,3,1) and actual[978]==1 and actual[979]==0,
            'Actual Start physical marker-predecessor bits from full weighted count equation')
    require((1+actual[978])%2==0,'Frozen996 premise fails: its forced Start marker contribution is EVEN')
    require((1+actual[979])%2==1,'Prospective997 repair has an odd Start marker contribution')
    return {'schema':'marker996_physical_label_correction_v1','script_sha256':sha(Path(__file__).read_bytes()),
            'frozen_failed_probe_sha256':FROZEN_SHA,'parent_sha256':PARENT_SHA,
            'seed_sha256':sha(seed.encode()),'actions_sha256':sha(encoded(actions)),
            'all942_tiles_sha256':sha(encoded(tiles)),'whole3297_coefficients_sha256':sha(encoded(c)),
            'complete_physical_to_packed_bit_map':mapping,
            'whole942_canonical_label_words':{'count':len(rows),'sha256':sha(encoded(rows))},
            'Start_physical978':actual[978],'Start_physical979':actual[979],
            'old_claimed_Start_marker_odd_bit':1,'actual_Start_marker996_odd_bit':0,
            'consequence':'Frozen996 finite checks used the wrong physical color component in the phase proof. Their marker-forcing and offset18 semantic conclusions are invalid; no complete996 native result is accepted.',
            'unaffected':'Earlier2011 tuple has no extra current physical label term at its marker. Fractional Start-South local lemma and its actual coefficient calibration are unchanged.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--write',action='store_true')
    args=parser.parse_args();raw=encoded(run());path=HERE/'CORRECTION.json'
    if args.write:path.write_bytes(raw)
    else:require(path.read_bytes()==raw,'Exact correction receipt')
    print(json.dumps({'status':'PASS','script_sha256':sha(Path(__file__).read_bytes()),'receipt_sha256':sha(raw)},sort_keys=True))


if __name__=='__main__':main()

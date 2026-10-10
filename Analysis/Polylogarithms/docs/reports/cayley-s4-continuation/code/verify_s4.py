#!/usr/bin/env python3
"""Verify the S4 word certificate, without a solver or numerical periods."""
from __future__ import annotations
import argparse
from fractions import Fraction
import json
from pathlib import Path
import hashlib
from word_algebra import (admissible,conjugate,plus,double_shuffle,cayley,
                          odd_projection,target)

def verify(path: Path) -> dict:
    certificate=json.loads(path.read_text())
    if certificate['schema']!='proveit.cayley-s4.word-certificate.v1':
        raise ValueError('Unknown certificate schema')
    residual=odd_projection(target())
    seen=set();n_ds=0;n_dual=0;n_divergent=0
    for row in certificate['rows']:
        coefficient=Fraction(row['coefficient'])
        if not coefficient: raise ValueError('Zero row in sparse certificate')
        if row['kind']=='double_shuffle':
            u,v=tuple(row['u']),tuple(row['v'])
            if len(u)+len(v)!=5: raise ValueError('Incorrect weight')
            key=('ds',u,v)
            raw=double_shuffle(u,v)
            n_ds+=1;n_divergent+=int(u==(0,))
        elif row['kind']=='cayley':
            w=tuple(row['word'])
            if len(w)!=5 or not admissible(w): raise ValueError('Invalid Cayley word')
            key=('cayley',w)
            raw=plus({w:1},cayley(w),-1)
            n_dual+=1
        else: raise ValueError('Unknown row kind')
        if key in seen: raise ValueError('Duplicate row identifier')
        seen.add(key)
        residual=plus(residual,odd_projection(raw),-coefficient)
    if residual:
        raise ArithmeticError(f'FAILED: {len(residual)} nonzero exact residual coordinates')
    return {'result':'PASS','arithmetic':'fractions.Fraction; no floating point',
            'double_shuffle_rows':n_ds,'single_divergence_rows':n_divergent,
            'cayley_rows':n_dual,'nonzero_residual_coordinates':0,
            'target_odd_coordinates':len(odd_projection(target())),
            'certificate_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}

def main() -> None:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('certificate',nargs='?',type=Path,
                    default=Path(__file__).resolve().parents[1]/'data/S4_certificate.json')
    ap.add_argument('--receipt',type=Path)
    args=ap.parse_args()
    result=verify(args.certificate)
    text=json.dumps(result,indent=2)+'\n'
    print(text,end='')
    if args.receipt: args.receipt.write_text(text)
if __name__=='__main__': main()

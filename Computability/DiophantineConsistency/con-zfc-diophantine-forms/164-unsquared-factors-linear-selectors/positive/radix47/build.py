#!/usr/bin/env python3
"""Bind the entire retained radix47 tuple, never mixed individual ports."""
import argparse,copy,hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
def construct(weight):
    src=ROOT.parent/f'equation_{weight}.json';g=json.loads(src.read_text())
    whole=json.loads((ROOT/'inherited'/'q1_bv.json').read_text())['coefficient_binding']
    g['coefficient_binding']=copy.deepcopy(whole)
    g['coefficient_binding']['path']='inherited/coefficients/'
    g.update(name='whole_radix47_inverse_lucas_'+weight,proof='PROOF.md',
        parent={'path':'../'+src.name,'sha256':hashlib.sha256(src.read_bytes()).hexdigest()},
        specialization='Entire incoming complemented-label radix47 tuple and its retained native bridge; not the conditional47 layout.')
    return g
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
    for weight in ('V2','bV'):
        p=ROOT/f'equation_{weight}.json';s=json.dumps(construct(weight),indent=2)+'\n'
        if a.check:
            if p.read_text()!=s:raise ValueError('whole47 rebuild mismatch '+p.name)
        else:p.write_text(s)
        print(p.name,'whole47')
if __name__=='__main__':main()

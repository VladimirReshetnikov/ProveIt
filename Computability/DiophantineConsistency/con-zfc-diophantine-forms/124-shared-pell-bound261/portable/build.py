#!/usr/bin/env python3
"""Rebuild either exact polynomial using only this directory and Python 3."""
from pathlib import Path
import argparse,json,sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'source/custom'))
from capped_pell import generate

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--variant',choices=['primary','sparse'],default='primary')
    p.add_argument('--output',type=Path)
    a=p.parse_args()
    out=a.output or HERE/'rebuilt'/a.variant
    if a.variant=='primary':
        result=generate(out,'cantor',12,96,True,True,False,False)
    else:
        result=generate(out,'cantor',16,96,False,False,False,True)
    reference=HERE/'equations'/a.variant
    checked=[]
    for rel in ['raw/equation.json','natural/equation.json',
                'natural/elimination_certificate.json','natural/expanded_polynomial.json']:
        if json.loads((out/rel).read_text())!=json.loads((reference/rel).read_text()):
            raise ValueError('Rebuilt artifact differs from frozen reference: '+rel)
        checked.append(rel)
    print(json.dumps({'variant':a.variant,'output':str(out),'metrics':result['natural'],
                      'exact_rebuild_matches':checked},indent=2))

if __name__=='__main__':main()

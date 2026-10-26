#!/usr/bin/env python3
"""Materialize the coarser A+1 center using the existing Ap1 register."""
from pathlib import Path
from collections import Counter
import argparse,hashlib,json
ROOT=Path(__file__).resolve().parent

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
    for directory in (ROOT,ROOT/'start_marker4177'):
        src=directory/'equation_bV.json';g=json.loads(src.read_text())
        g['source']=[row for row in g['source'] if row[0]!='A']
        for row in g['source']:
            if row[0]=='g0':row[2]='Ap1'
        g.update(name=g['name'].replace('88_degree224','87_degree228'),operations=87,exact_degree=228,
            operation_breakdown=dict(Counter(row[1] for row in g['source'])),center_offset=1,
            parent={'path':'equation_bV.json','sha256':hashlib.sha256(src.read_bytes()).hexdigest()},
            proof='PLUS_ONE.md' if directory==ROOT else '../PLUS_ONE.md',
            generation='Replace AUE by (A+1)UE using the already-live Ap1; no new A addition.')
        out=directory/'equation_plus1_bV.json';data=json.dumps(g,indent=2)+'\n'
        if a.check:
            if out.read_text()!=data:raise ValueError('plus-one rebuild mismatch')
        else:out.write_text(data)
        print(str(out.relative_to(ROOT)),g['operations'],g['exact_degree'])
if __name__=='__main__':main()

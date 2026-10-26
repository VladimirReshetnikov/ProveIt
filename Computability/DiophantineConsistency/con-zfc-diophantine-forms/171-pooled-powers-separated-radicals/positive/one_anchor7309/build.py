#!/usr/bin/env python3
"""Bind the entire frozen one-anchor tuple to the exact verified free-port graph."""
from pathlib import Path
import argparse,hashlib,json
ROOT=Path(__file__).resolve().parent

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
    parent=ROOT/'../equation_bV.json';g=json.loads(parent.read_text())
    native=json.loads((ROOT/'snapshot/candidates/one-page-one-anchor7309/polynomial.json').read_text())
    g['coefficient_binding']=native['coefficient_binding'];b=g['coefficient_binding']
    b['endianness']='big';b['ordinary_proof']='snapshot/research/one-anchor-independent/PROOF.md';b['certificate']='snapshot/research/one-anchor-independent/certificate.json'
    g['parent']={'path':'../equation_bV.json','sha256':hashlib.sha256(parent.read_bytes()).hexdigest()}
    g['name']='inverse_trace85_degree232_one_anchor7309';g['proof']='PROOF.md'
    data=json.dumps(g,indent=2)+'\n';out=ROOT/'equation_bV.json'
    if a.check:
        if out.read_text()!=data:raise ValueError('specialization reconstruction mismatch')
    else:out.write_text(data)
    print(g['operations'],g['exact_degree'],b['raw_bytes'])
if __name__=='__main__':main()

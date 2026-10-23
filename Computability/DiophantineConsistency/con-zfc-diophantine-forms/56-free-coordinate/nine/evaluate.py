#!/usr/bin/env python3
"""Evaluate the fixed nine-positive polynomial modulo a supplied positive modulus."""
import argparse,json
from math import prod
from pathlib import Path
from circuit import evaluate
from materialize import load_ports
ROOT=Path(__file__).resolve().parent

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--modulus',type=int,required=True);ap.add_argument('coordinates',nargs=9,type=int,metavar='INTEGER');args=ap.parse_args()
    if args.modulus<=1:ap.error('modulus must exceed one')
    p=args.modulus;body=json.loads((ROOT/'generated/calibrated_absorbed_positive.json').read_text());ports=[z%p for z in load_ports()]
    fixed={'base_scale':pow(2,body['base_scale_exponent'],p),'threshold_scale':pow(2,body['threshold_scale_exponent'],p)}
    for rec in body['coefficient_recipes']:fixed[rec['name']]=sum(t['coefficient']*prod(pow(z,e,p) for z,e in zip(ports,t['powers'])) for t in rec['terms'])%p
    values=dict(zip(body['variables'],args.coordinates));result,_=evaluate(body,fixed,values,p)
    print(json.dumps({'variables':values,'modulus':p,'residue':result,'all_coordinates_strictly_positive':all(z>0 for z in args.coordinates),'interpretation':'A modular zero is not evidence of an integer zero.'},indent=2))
if __name__=='__main__':main()

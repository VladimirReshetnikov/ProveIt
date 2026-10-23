#!/usr/bin/env python3
"""Evaluate either literal fixed polynomial modulo a supplied positive integer."""
import argparse
import json
from pathlib import Path
from independent_check import constants,evaluate

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('circuit',choices=['p14_degree26','p14_degree30'])
parser.add_argument('--modulus',type=int,required=True)
parser.add_argument('inputs',type=int,nargs=14)
args=parser.parse_args()
if args.modulus<2:parser.error('modulus must be at least2')
if min(args.inputs)<1:parser.error('all14 inputs must be strictly positive')
here=Path(__file__).resolve().parent
d=json.loads((here/'circuits'/(args.circuit+'.json')).read_text())
ports={k:v%args.modulus for k,v in constants().items()}
value,_=evaluate(d,dict(zip(d['variables'],args.inputs)),ports,args.modulus)
print(value)

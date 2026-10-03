#!/usr/bin/env python3
"""Explicit structural loader. --A is the raw interface; --halves L R pays
external exponentiation and does not claim constant-cost arithmetic loading.
The JSON is an exact shared-tree descriptor, not an expanded population.
"""
import argparse,json,sys
if hasattr(sys,"set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)  # This explicit loader accepts arbitrary finite decimal inputs.
from pathlib import Path
R=Path(__file__).resolve().parent

def descriptor(A):
    if type(A) is not int or A<1:raise ValueError('raw A must be a positive integer')
    entry=json.loads((R/'literal2.json').read_text())['entry']
    return {'format':'sparse-configuration-motif-v1','raw_A':A,'root':3,
      'motifs':[{'label':h,'objects':[],'children':[]} for h in ('1','2','s')]+[
        {'label':'skin','objects':[[entry,1]],
         'children':[{'motif':0,'multiplicity':A+1},{'motif':1,'multiplicity':1},{'motif':2,'multiplicity':1}]}],
      'generic_motif_positive_edge_coordinates':{'c:3:0':A,'c:3:1':0,'c:3:2':0},
      'expanded_membrane_count':A+4,
      'acceptance':'There exists a maximally parallel run ending in global quiescence.'}

def main():
    ap=argparse.ArgumentParser(description=__doc__);group=ap.add_mutually_exclusive_group(required=True)
    group.add_argument('--A',type=int);group.add_argument('--halves',nargs=2,type=int,metavar=('L','R'))
    args=ap.parse_args()
    if args.halves is not None:
        L,RR=args.halves
        if min(L,RR)<0:ap.error('half tapes must be nonnegative')
        A=2**L*3**RR
    else:A=args.A
    try:d=descriptor(A)
    except ValueError as e:ap.error(str(e))
    if args.halves is not None:d['external_preprocessing']={'L':L,'R':RR,'map':'A=2^L*3^R','A_bit_length':A.bit_length(),'charged_separately':True}
    print(json.dumps(d,indent=2))
if __name__=='__main__':main()

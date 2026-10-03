#!/usr/bin/env python3
"""Affine structural loader for raw binary half-tape integers L,R >=0."""
import argparse,json,sys
from pathlib import Path
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
R=Path(__file__).resolve().parent

def descriptor(L,RR):
    if any(type(x) is not int or x<0 for x in (L,RR)):raise ValueError('L and R must be natural integers')
    return {'format':'sparse-configuration-motif-v1','L':L,'R':RR,'root':4,
      'motifs':[{'label':h,'objects':[],'children':[]} for h in ('1','2','3','s')]+[
        {'label':'skin','objects':[['init_clear_T',1]],'children':[{'motif':i,'multiplicity':n} for i,n in enumerate((L+1,RR+1,1,1))]}],
      'generic_motif_positive_edge_coordinates':{'c:4:0':L,'c:4:1':RR,'c:4:2':0,'c:4:3':0},
      'expanded_membrane_count':L+RR+5,
      'acceptance':'Some maximally parallel computation globally halts; a HALT object by itself is insufficient.'}
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('L',type=int);p.add_argument('R',type=int);a=p.parse_args()
    try:d=descriptor(a.L,a.R)
    except ValueError as e:p.error(str(e))
    print(json.dumps(d,indent=2))

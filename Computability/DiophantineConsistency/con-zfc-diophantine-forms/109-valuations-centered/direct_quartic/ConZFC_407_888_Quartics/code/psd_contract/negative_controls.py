#!/usr/bin/env python3
"""Reject corrupted SOS weights and identities using the independent checker."""
from copy import deepcopy
from pathlib import Path
import argparse
import json
from check import verify


def main():
    p=argparse.ArgumentParser()
    p.add_argument('source',type=Path)
    p.add_argument('target_dir',type=Path)
    a=p.parse_args()
    source=json.loads(a.source.read_text())
    target=json.loads((a.target_dir/'equation.json').read_text())
    original=json.loads((a.target_dir/'elimination_certificate.json').read_text())
    index=next(i for i,s in enumerate(original['steps']) if s['nonnegative_certificate']['squares'])
    controls=[]
    for mode in ('altered_weight','negative_weight'):
        cert=deepcopy(original)
        weight=cert['steps'][index]['nonnegative_certificate']['squares'][0]['weight']
        weight[0]=weight[0]+weight[1] if mode=='altered_weight' else -abs(weight[0])
        try:
            verify(source,target,cert)
        except ValueError as error:
            controls.append({'control':mode,'rejected':True,'reason':str(error)})
        else:
            raise ValueError('corrupt certificate accepted: '+mode)
    print(json.dumps({'verified':True,'controls':controls},indent=2))


if __name__=='__main__':main()

#!/usr/bin/env python3
"""Restore a final tuple to the immediate source through the six exact maps."""
from pathlib import Path
import argparse,json
ROOT=Path(__file__).resolve().parent.parent
def evaluate(terms,x):
    total=0
    for c,m in terms:
        value=c
        for i in m:value*=x[i]
        total+=value
    return total
def main():
    p=argparse.ArgumentParser();p.add_argument('endpoint',choices=['self_power235','self_power236','shared_error234']);p.add_argument('tuple',type=Path);a=p.parse_args()
    folder=ROOT/'equations'/a.endpoint;e=json.loads((folder/'equation.json').read_text());x=json.loads(a.tuple.read_text())
    if len(x)!=len(e['variables']) or not all(type(v)is int for v in x):raise ValueError('wrong tuple domain or dimension')
    cert=json.loads((folder/'certificate.json').read_text())
    for st in reversed(cert):
        z=[0]*len(st['variables_before'])
        for index,value in zip(st['retained_variables'],x):z[index]=value
        v=st['pivot_variable'];z[v]=evaluate(st['restoration'],z)
        x=z.copy()
        for w,c in st['direction']:
            if w!=v:x[w]=z[w]+c*z[v]
    print(json.dumps(x))
if __name__=='__main__':main()

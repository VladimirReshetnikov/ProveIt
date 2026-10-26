#!/usr/bin/env python3
"""Reconstruct the literal circuits from source227 and unit projections.

Default: compare every reconstructed graph with its delivered bytes.
--output DIR: write reconstructed circuits under a separate destination.
"""
import argparse,json
from pathlib import Path

ROOT=Path(__file__).resolve().parent
def canonical(o):return (json.dumps(o,sort_keys=True,separators=(',',':'))+'\n').encode()
def reconstruct(source,p):
    nodes=[];registry={}
    def node(key):
        if key not in registry:registry[key]=len(nodes);nodes.append(list(key))
        return registry[key]
    def number(c):return node(('const',c))
    def operation(op,a,b):
        av=nodes[a][1] if nodes[a][0]=='const' else None;bv=nodes[b][1] if nodes[b][0]=='const' else None
        if av is not None and bv is not None:return number(av+bv if op=='add' else av*bv)
        if op=='add':
            if av==0:return b
            if bv==0:return a
        else:
            if av==0 or bv==0:return number(0)
            if av==1:return b
            if bv==1:return a
        return node((op,*sorted((a,b))))
    definitions={s['variable']:s['restoration'] for s in p['pivots']};mapped={v:node(('input',i)) for i,v in enumerate(p['free'])};active=set()
    def coordinate(v):
        if v in mapped:return mapped[v]
        if v in active:raise ValueError('cyclic unit projection')
        active.add(v);r=expression(definitions[v]);active.remove(v);mapped[v]=r;return r
    def expression(terms):
        result=number(0)
        for coeff,monomial in sorted(terms,key=lambda t:tuple(t[1])):
            term=number(coeff)
            for v in monomial:term=operation('mul',term,coordinate(v))
            result=operation('add',result,term)
        return result
    residuals=[expression(source['residuals'][i]['terms']) for i in p['retained_rows']]
    output=number(0)
    for r in residuals:output=operation('add',output,operation('mul',r,r))
    for v in range(len(source['variables'])):coordinate(v)
    return {'schema':'integer_binary_arithmetic_graph_v1','domain':'unrestricted integers','variables':[source['variables'][v]['name'] for v in p['free']],
            'nodes':nodes,'output':output,'residual_roots':residuals,'source_coordinate_roots':[mapped[v] for v in range(len(source['variables']))]}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path);a=ap.parse_args();source=json.loads((ROOT/'source227.json').read_text());count=0
    for folder in sorted(ROOT.glob('P[0-9]*')):
        if not folder.is_dir():continue
        p=json.loads((folder/'projection.json').read_text());data=canonical(reconstruct(source,p))
        if data!=(folder/'circuit.json').read_bytes():raise ValueError('circuit rebuild differs: '+folder.name)
        if a.output:
            dest=a.output/folder.name/'circuit.json';dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
        count+=1
    print(json.dumps({'status':'PASS','byte_identical_circuits':count}))

if __name__=='__main__':main()

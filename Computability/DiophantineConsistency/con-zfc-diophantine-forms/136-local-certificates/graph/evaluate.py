#!/usr/bin/env python3
"""Evaluate a supplied integer point, or lift a point of the source system.

For --lift, the canonical tree flow satisfies the polynomial identity
2 P(lift(x)) = sum_i R_i(x)^2 + (sum_i R_i(x))^2.
This is an evaluator and a witness map, not a solvability decision algorithm.
"""
import argparse
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent

def require(condition,message):
    if not condition: raise ValueError(message)

def monomial(indices,values):
    product=1
    for i in indices: product*=values[i]
    return product

def value(terms,point):
    return sum(c*monomial(m,point) for c,m in terms)

def lift(point,source,parent,old,new,certificate):
    require(len(point)==len(source['variables']),'Source-point dimension')
    norm=[]
    for descriptor in old['normalization']['variables']:
        kind=descriptor['kind']
        if kind=='original': norm.append(point[descriptor['source_index']])
        elif kind=='constant': norm.append(descriptor['value'])
        elif kind=='scale': norm.append(descriptor['coefficient']*point[descriptor['variable']])
        else: raise ValueError('Normalization kind')
    parent_point=[None]*len(parent['variables'])
    for row in old['equality_cycles']:
        for i in row['aliases']: parent_point[i]=norm[row['normalized_variable']]
    for i in old['unit_path']:parent_point[i]=1
    divergence=[0]*len(old['vertices']);adjacency=[[] for _ in old['vertices']]
    for ei,e in enumerate(old['edges']):
        if e['kind']=='prescribed':
            c=e['coefficient']*monomial(e['monomial'],parent_point)
            divergence[e['tail']]+=c;divergence[e['head']]-=c
        else:
            adjacency[e['tail']].append((e['head'],ei))
            adjacency[e['head']].append((e['tail'],ei))
    for block in old['row_blocks']+[old['hub_vertices']]:
        root=block[0];tree_parent={root:None};order=[root]
        for v in order:
            for w,ei in adjacency[v]:
                if w not in tree_parent: tree_parent[w]=(v,ei);order.append(w)
        require(set(order)==set(block),'Malformed free tree')
        for v in reversed(order[1:]):
            w,ei=tree_parent[v];edge=old['edges'][ei]
            sign=edge['coefficient']*(1 if edge['tail']==v else -1)
            require(sign in (-1,1) and len(edge['monomial'])==1,'Invalid free edge')
            flow=-divergence[v]*sign
            parent_point[edge['monomial'][0]]=flow
            divergence[w]+=divergence[v];divergence[v]=0
    require(all(type(x)is int for x in parent_point),'Unassigned parent coordinate')
    result=[None]*len(new['variables'])
    for i,t in enumerate(certificate['parent_to_child']):
        if t is not None:
            require(result[t] is None or result[t]==parent_point[i],'Conflicting alias lift')
            result[t]=parent_point[i]
    for row in certificate['equality_cycles']:
        for i in row['aliases']: result[i]=norm[row['normalized_variable']]
    for i in certificate['unit_path']:result[i]=1
    require(all(type(x)is int for x in result),'Unassigned new coordinate')
    residuals=[value(row['terms'],point) for row in source['residuals']]
    expected=sum(r*r for r in residuals)+sum(residuals)**2
    actual=value(new['terms'],result)
    require(2*actual==expected,'Canonical lift energy identity failed')
    return result,actual,expected

def main():
    p=argparse.ArgumentParser();p.add_argument('point',type=Path)
    p.add_argument('--profile',default='principal985')
    p.add_argument('--lift',action='store_true');p.add_argument('--output',type=Path)
    args=p.parse_args()
    profiles={p['name']:p for p in json.loads((HERE/'PROFILES.json').read_text())}
    require(args.profile in profiles,'Unknown profile')
    profile=profiles[args.profile];d=HERE/args.profile;parent_directory=HERE/'parents'/args.profile
    point=json.loads(args.point.read_text())
    require(isinstance(point,list) and all(type(x)is int for x in point),'Point must be an array of integers')
    new=json.loads((d/'polynomial.json').read_text())
    if args.lift:
        result,answer,expected=lift(point,json.loads((HERE/profile['source']).read_text()),
           json.loads((parent_directory/'polynomial.json').read_text()),json.loads((parent_directory/'certificate.json').read_text()),
           new,json.loads((d/'certificate.json').read_text()))
        output={'profile':args.profile,'lifted_point':result,'value':answer,'twice_source_energy':expected}
    else:
        require(len(point)==len(new['variables']),'Point dimension')
        output={'profile':args.profile,'value':value(new['terms'],point)}
    text=json.dumps(output,separators=(',',':'))+'\n'
    if args.output:args.output.write_text(text)
    else:print(text,end='')

if __name__=='__main__':main()

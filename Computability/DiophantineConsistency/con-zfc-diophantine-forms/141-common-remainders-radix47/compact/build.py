#!/usr/bin/env python3
"""Rebuild three literal positive-integer carrier circuits from pinned data."""
from pathlib import Path
from collections import Counter
import argparse, copy, hashlib, json

ROOT=Path(__file__).resolve().parent
VARIANTS=[('XY',78,78,626),('XY',79,79,464),('q4',79,80,460)]

def build(mode,parent_count,operations,degree):
    file=ROOT/'upstream'/'parent'/f'equation{parent_count}.json'
    data=copy.deepcopy(json.loads(file.read_text()))
    rows=[]
    for name,op,a,b in data['source']:
        if mode=='XY':
            if name=='Y2':name,op,a,b='D','*','X','Y'
            elif name=='V0':a,b='D','Y'
            else:a,b=('D' if a=='Y2' else a),('D' if b=='Y2' else b)
        elif name in ('P1mu2','mu2inner'):
            a,b=('D' if a=='Y2' else a),('D' if b=='Y2' else b)
        rows.append([name,op,a,b])
        if mode=='q4' and name=='q2':rows.append(['D','*','q2','q2'])
    if len(rows)!=operations:raise ValueError('Unexpected circuit row count')
    data.update(name=f'carrier_{mode}_{operations}_{degree}',source=rows,
                operations=operations,operation_breakdown=dict(sorted(Counter(r[1] for r in rows).items())),
                exact_degree=degree,carrier_denominator='X*Y' if mode=='XY' else 'q^4',
                proof='DENOMINATOR_PROOF.md',parent=f'upstream/parent/equation{parent_count}.json',
                parent_sha256=hashlib.sha256(file.read_bytes()).hexdigest())
    return data

def encode(data):return json.dumps(data,indent=2)+'\n'

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');p.add_argument('--output-dir',type=Path,default=ROOT)
    a=p.parse_args();a.output_dir.mkdir(parents=True,exist_ok=True);results=[]
    for mode,parent_count,ops,degree in VARIANTS:
        name=f'equation_{ops}_{degree}.json';value=encode(build(mode,parent_count,ops,degree));target=a.output_dir/name
        if a.check:
            if target.read_text()!=value:raise ValueError('Rebuild differs: '+name)
        else:target.write_text(value)
        results.append({'file':name,'operations':ops,'exact_degree':degree,'bytes':len(value.encode()),'checked':a.check})
    print(json.dumps(results,indent=2))

if __name__=='__main__':main()

#!/usr/bin/env python3
"""Compose polynomial centering with the exact bounded source172 free chart."""
from pathlib import Path
from collections import Counter
import argparse,hashlib,json
ROOT=Path(__file__).resolve().parent

def construct(mode,tuple_name):
    src=ROOT/'parent/positive10_degree214_ops87.json';g=json.loads(src.read_text());rows=[]
    for name,op,a,b in g['source']:
        if name=='L':
            if mode=='centerA':rows.append(['A','+','Am1',1])
            rows.extend([['g0','*','A' if mode=='centerA' else 'Ap1','UE'],['bB','*','cTR','Bt'],['bB_g0','+','bB','g0']]);continue
        if name=='LBt':a,b='V','bB_g0'
        rows.append([name,op,a,b])
    if tuple_name=='start4177':
        native=json.loads((ROOT/'../start_marker4177/snapshot/candidates/one-page-start-marker4177/polynomial.json').read_text())
        g['coefficient_binding']=native['coefficient_binding'];g['coefficient_binding']['path']='../start_marker4177/coefficients';g['coefficient_binding']['endianness']='big'
        g['coefficient_binding']['ordinary_proof']='../start_marker4177/snapshot/research/start-marker-independent/PROOF.md'
        g['coefficient_binding']['certificate']='../start_marker4177/snapshot/research/start-marker-independent/certificate.json'
    else:
        g['coefficient_binding']['path']='parent/'+g['coefficient_binding']['path'];g['coefficient_binding']['endianness']='little'
    g.update(name=mode+'_'+tuple_name,mode=mode,tuple_name=tuple_name,source=rows,
      operations=len(rows),exact_degree=206 if mode=='centerA' else 210,
      operation_breakdown=dict(sorted(Counter(row[1] for row in rows).items())),
      parent={'path':str(src.relative_to(ROOT)),'sha256':hashlib.sha256(src.read_bytes()).hexdigest()},
      proof='PROOF.md',generation='Polynomial AUE or (A+1)UE carrier centering composed with source172 free Y=s,lambda=q inverse-trace front.',
      status='Ordinary proof at separately retained whole-tuple native/refutation calibration; no formal-kernel replay.')
    return g

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
    for mode in ('centerA','centerAp1'):
        for t in ('radix67','start4177'):
            g=construct(mode,t);p=ROOT/(g['name']+'.json');s=json.dumps(g,indent=2)+'\n'
            if a.check:
                if p.read_text()!=s:raise ValueError('rebuild '+p.name)
            else:p.write_text(s)
            print(p.name,g['operations'],g['exact_degree'])
if __name__=='__main__':main()

#!/usr/bin/env python3
"""Deterministically rebuild the complete 93-gate equation (no network)."""
import argparse,json,hashlib
from pathlib import Path
from collections import Counter
HERE=Path(__file__).resolve().parent

def build():
    raw=(HERE/'upstream/parent_equation.json').read_bytes()
    p=json.loads(raw); rows=[]
    for row in p['source'][:78]:
        n,op,a,b=row
        if n=='I2':
            rows += [['ID','*','I','Dtau'],['I2D','*','I','ID']];continue
        if n=='DpI2':row=[n,op,a,'I2D']
        if n=='HI':
            rows += [['A','+','Am1',1],['Pcenter','*','A','ID']];continue
        if n=='L':continue
        if n=='qm1L':row=[n,op,a,'cTR']
        if n=='Hn':
            rows += [['nVP','+','nV','Pcenter']];row=[n,op,a,'nVP']
        rows.append(row)
    rows += [
        ['M2','*','Mtot','Mtot'],['dM2','*','delta','M2'],
        ['Dprod','*','Dtau','Df'],['fa','*','dM2','Dprod'],
        ['fc','*','M2','Dnum'],['Z2','*','Znum','Znum'],
        ['fs','*','delta','Z2'],['sumac','+','fa','fc'],
        ['diff','-','fs','sumac'],['diff2','*','diff','diff'],
        ['ac','*','fa','fc'],['ac4','*',4,'ac'],['N','-','diff2','ac4']]
    d={v:1 for v in p['witnesses']}|{v:0 for v in p['fixed_numerals']}
    for n,op,a,b in rows:
        da,db=(0 if type(v)is int else d[v] for v in (a,b))
        d[n]=da+db if op=='*' else max(da,db)
    p.update(name='ten_positive_saturated_centered',source=rows,operations=len(rows),
      operation_breakdown=dict(Counter(r[1] for r in rows)),syntactic_degree=d['N'],
      exact_degree=278,proof='PROOF.md',
      proof_status='Ordinary unbounded arithmetic equivalence, relative to the pinned native/source interface; no new formalized ZFC derivation.',
      parent_sha256=hashlib.sha256(raw).hexdigest(),register_degrees=d,
      coefficient_binding=json.loads((HERE/'coefficients/BINDING.json').read_text()))
    return (json.dumps(p,indent=2,sort_keys=True)+'\n').encode()

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
    output=build();path=HERE/'equation.json'
    if args.check:
        if path.read_bytes()!=output:raise ValueError('complete deterministic equation mismatch')
    else:path.write_bytes(output)
    print(json.dumps({'status':'PASS','check':args.check,'sha256':hashlib.sha256(output).hexdigest()}))

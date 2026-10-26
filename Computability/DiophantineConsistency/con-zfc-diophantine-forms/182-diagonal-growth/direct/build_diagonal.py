#!/usr/bin/env python3
"""Emit the diagonal-power C222 quartic from an authenticated P215 source.

Only standard-library Python is required. No search for a zero is performed.
The semantic replacement is proved in DIAGONAL_PROOF.md; finite algebra alone
does not prove the inherited Pell and logical calibration.
"""
from __future__ import annotations
from pathlib import Path
import argparse, copy, hashlib, json
from collections import defaultdict

ROOT=Path(__file__).resolve().parent
PARENT_SHA='8d919a1e5d6a802765b6d010c0140fb1d83c3d36d211b209b7a8d2fb3f3fb6f6'

def require(test,msg):
    if not test: raise ValueError(msg)

def read_poly(row): return {tuple(m):c for c,m in row['terms']}
def ts(p): return [[c,list(m)] for m,c in sorted(p.items()) if c]
def add(*ps):
    d=defaultdict(int)
    for p in ps:
        for m,c in p.items(): d[m]+=c
    return {m:c for m,c in d.items() if c}
def mul(p,q):
    d=defaultdict(int)
    for m,c in p.items():
        for n,e in q.items():d[tuple(sorted(m+n))]+=c*e
    return {m:c for m,c in d.items() if c}
def canonical(x): return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def display(p):
    out=[]
    for m,c in sorted(p.items()):
        if not c: continue
        atoms=[]
        for i in sorted(set(m)):
            k=m.count(i); atoms.append('x'+str(i)+(('^'+str(k)) if k>1 else ''))
        a='*'.join(atoms)
        a=(str(abs(c))+'*'+a if a and abs(c)!=1 else a) if a else str(abs(c))
        out.append((' - ' if c<0 else ' + ')+a)
    s=''.join(out)
    return ('-'+s[3:] if s.startswith(' - ') else s[3:]) if s else '0'

def build(output, coefficient=464, horizon=464):
    raw=(ROOT/'principal/equation.json').read_bytes()
    require(hashlib.sha256(raw).hexdigest()==PARENT_SHA,'parent hash mismatch')
    parent=json.loads(raw)
    require(len(parent['variables'])==215 and len(parent['residuals'])==154,'parent shape')
    rows=[read_poly(r) for r in parent['residuals']]
    expected={96:{():1,(0,0):1,(0,132):-2,(139,):1},
      97:{(0,182):-1,(2,):1,(139,140):1,(181,):-1},
      130:{():-128,(0,):1,(185,185):-4},
      152:{(0,0):-1,(214,):1},153:{(93,):1,(214,214):-1}}
    for i,p in expected.items():require(rows[i]==p,'parent interface '+str(i))
    require(parent['variables'][93]['name']=='growth.index','growth index port')
    require(parent['variables'][132]['name']=='shared.A','Pell center port')
    # At the principal's final integral chart: t=x0, F=x2, K=x93, A=x132.
    replacement={
      96:{():1,(93,93):1,(93,132):-2,(139,):1},
      97:{(93,182):-1,(2,):1,(139,140):1,(181,):-1},
      128:add(rows[128],{(0,0):1,(93,93):-1}),
      130:{():-horizon,(0,):1,(185,185):-1},
      152:{(0,0):-coefficient,(93,):1}}
    eq=copy.deepcopy(parent)
    eq['schema']='conzfc-diagonal-power-quartic-v1'
    eq['variant']='diagonal_'+str(coefficient)+'_horizon_'+str(horizon)
    eq['variables']=eq['variables'][:-1]
    eq['parent_equation_sha256']=PARENT_SHA
    eq.pop('growth_multiplier',None)
    eq['diagonal_coefficient']=coefficient
    eq['horizon_minimum']=horizon
    eq['residuals']=[]
    for i,r in enumerate(parent['residuals'][:-1]):
        nr=copy.deepcopy(r);nr['terms']=ts(replacement.get(i,rows[i]))
        if i==152:nr['label']='growth.diagonal_index'
        eq['residuals'].append(nr)
    polys=[read_poly(r) for r in eq['residuals']]
    live={v for p in polys for m in p for v in m}
    require(live==set(range(214)),'every listed variable must be live')
    require(max(len(m) for p in polys for m in p)<=2,'not quadratic residuals')
    expansion=add(*(mul(p,p) for p in polys))
    metrics={'variables':214,'residuals':153,'degree':max(map(len,expansion)),
      'monomials':len(expansion),'height':max(map(abs,expansion.values())),
      'residual_monomials':sum(map(len,polys)),
      'residual_height':max(abs(c) for p in polys for c in p.values()),
      'domain':'unrestricted integers'}
    certificate={'schema':'diagonal-power-source-delta-v1','parent_sha256':PARENT_SHA,
      'changed_rows':[{'row':i,'before':ts(rows[i]),'after':ts(replacement[i])} for i in sorted(replacement)],
      'deleted_rows':[153],'deleted_variables':[214],
      'semantic_ports':{'t':0,'F':2,'K':93,'A':132,'horizon_root':185,
        'power_remainder_divisor':139,'power_quotient':140,
        'K_pair_X_minus_AY':181,'K_pair_Y':182,'K_pair_X_minus_one':183},
      'frame_delta':'one occurrence of growth-base t^2 is replaced by K^2; existing index K^2 remains',
      'proof':'DIAGONAL_PROOF.md'}
    output.mkdir(parents=True,exist_ok=True)
    for name,obj in [('equation.json',eq),('expanded_polynomial.json',{'schema':'sparse-polynomial-v1','variables':214,'terms':ts(expansion)}),('metrics.json',metrics),('source_delta.json',certificate)]:
        (output/name).write_bytes(canonical(obj))
    lines=['Domain: all 214 variables are unrestricted integers.','P(x0,...,x213) = sum(Rj^2, j=0,...,152) = 0.','']
    lines += ['R'+str(i)+' = '+display(p) for i,p in enumerate(polys)]
    (output/'residuals.txt').write_text('\n'.join(lines)+'\n')
    (output/'variables.tsv').write_text('index\tname\n'+''.join(str(i)+'\t'+v['name']+'\n' for i,v in enumerate(eq['variables'])))
    receipt={'status':'PASS','metrics':metrics,'equation_sha256':hashlib.sha256((output/'equation.json').read_bytes()).hexdigest(),'expanded_sha256':hashlib.sha256((output/'expanded_polynomial.json').read_bytes()).hexdigest()}
    print(json.dumps(receipt,indent=2))
    return receipt

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,default=ROOT/'diagonal214')
    p.add_argument('--coefficient',type=int,default=464);p.add_argument('--horizon',type=int,default=464)
    a=p.parse_args();build(a.output,a.coefficient,a.horizon)

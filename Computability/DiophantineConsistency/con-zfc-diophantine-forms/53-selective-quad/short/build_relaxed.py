#!/usr/bin/env python3
"""Produce a 15-variable relaxed-rank circuit from the pinned P75 DAG."""
from pathlib import Path
import json, hashlib
ROOT=Path(__file__).resolve().parent
SRC=ROOT/'upstream/circuits__p75_sos.json'
p75=json.loads(SRC.read_text())
for count in (74,72):
    c=json.loads(SRC.read_text())
    prefix=[g for g in c['source'] if g[0]!='strong_square_scaled']
    prefix=prefix[:next(i for i,g in enumerate(prefix) if g[0]=='main_index')]
    if len(prefix)!=61: raise ValueError('Unexpected inherited kernel size')
    if count==74:
        groups=[['main_index','*','norm_main','norm_index'],['main_index_transport','*','main_index','norm_transport']]
        rs=[('r0','norm_first',1),('ra','norm_aux',1),('rs','R16','aux_reduced_coefficient'),('rmit','main_index_transport',1)]
    else:
        groups=[['first_main','*','norm_first','norm_main'],['aux_index','*','norm_aux','norm_index'],['aux_index_transport','*','aux_index','norm_transport']]
        rs=[('r01','first_main',1),('rait','aux_index_transport',1),('rs','R16','aux_reduced_coefficient')]
    gs=prefix+groups+[[n,'-',l,r] for n,l,r in rs]+[[n+'2','*',n,n] for n,_,_ in rs]
    prev=rs[0][0]+'2'
    for idx,(n,_,_) in enumerate(rs[1:]):
        dest='polynomial' if idx==len(rs)-2 else f'sum{idx}'
        gs.append([dest,'+',prev,n+'2']);prev=dest
    if len(gs)!=count: raise ValueError('Unexpected operation count')
    c.update(name=f'p{count}_relaxed_rank_sos',source=gs,output='polynomial',exact_degree=56 if count==74 else 80)
    c['coefficient_binding']={'file':'COEFFICIENT_BINDING.json','aliases':{'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'},'warning':'Use the entire Wang943 121-by-8801 tuple. MF is shifted.'}
    c['provenance']={'repository':'VladimirReshetnikov/ProveIt','commit':'124c07c0b77a9e20e84676514d8b1ff78536ea3f','source':'upstream/circuits__p75_sos.json','sha256':hashlib.sha256(SRC.read_bytes()).hexdigest(),'change':'Replace normalized strong residual by I^2-Delta*(f^2-1), prune Delta*I^2, and group the remaining unit constraints.'}
    c['proof_boundary']='Ordinary mathematical existence equivalence through the inherited relaxed-Pell rank theorem. Not same-coordinate zero equivalence and not newly Lean checked. Finite algebra/circuit checks do not certify compiler semantics.'
    (ROOT/f'p{count}_relaxed.json').write_text(json.dumps(c,indent=2)+'\n')
system=json.loads((ROOT/'p74_relaxed.json').read_text())
system.update(name='relaxed15_system61',source=prefix,comparisons=[['norm_first',1],['norm_main',1],['norm_aux',1],['norm_index',1],['norm_transport',1],['R16','aux_reduced_coefficient']],residual_exact_degrees=[22,18,28,7,2,22],exact_maximum_degree=28)
for k in ('output','exact_degree'):system.pop(k,None)
(ROOT/'relaxed15_system61.json').write_text(json.dumps(system,indent=2)+'\n')

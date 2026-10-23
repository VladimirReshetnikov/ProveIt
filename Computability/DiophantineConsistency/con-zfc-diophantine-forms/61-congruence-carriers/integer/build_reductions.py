#!/usr/bin/env python3
"""Build two literal integer reductions of package 57's quartic45.

This exact checker uses only Python's standard library.  It checks each
elimination against a source residual and proves the degree certificates by
expanding the entire sum of squares with symbolic fixed ports.
"""
import json, hashlib
from pathlib import Path
import eliminate as e

ROOT=Path(__file__).resolve().parent
q='(beta*J+1)'
H='(4*a+3)'
pe='1+eta_pos1**2+eta_pos2**2+eta_pos3*(eta_pos3+1)'
pz='1+zeta_pos1**2+zeta_pos2**2+zeta_pos3*(zeta_pos3+1)'

DEFINITIONS_37=[
 ('Baux','I**2'),('C2','c**2'),('F2','f**2'),
 ('N',q+'*(L+1)'),('w','u**2'),('X','D-a*c-gamma*'+H),
 ('eta',pe),('zeta',pz),
]
DEFINITIONS_34=[
 ('L',q+'**2-1'),('N',q+'**3'),('X','w*'+q),
 ('D','w*'+q+'+a*c+gamma*'+H),('Delta','a**2+'+H),
 ('C2','c**2'),('F2','f**2'),('Baux','I**2'),
 ('g','y**2-V**2'),('eta',pe),('zeta',pz),
]

def canonical(defs,target_degree,name):
    eqs=e.equations();history=[]
    for var,text in defs:
        rhs=e.parse(text)
        relation=e.sub(e.var(var),rhs)
        matches=[i for i,p in enumerate(eqs) if p==relation or p==e.scale(relation,-1)]
        if len(matches)!=1:
            raise RuntimeError(f'{var}: expected one exact unit definition, got {matches}')
        index=matches[0]
        eqs,r=e.eliminate(eqs,var,index)
        if r!=rhs:raise RuntimeError('Wrong recovered definition')
        history.append({'variable':var,'definition':text,'deleted_residual_index':index})
    degrees=list(map(e.degree,eqs))
    if max(degrees)!=target_degree//2:raise RuntimeError('Degree budget failed')
    poly={}
    for p in eqs:poly=e.add(poly,e.mul(p,p))
    if e.degree(poly)!=target_degree:raise RuntimeError('Exact degree failed')
    mon={'r':2,'c':4} if name=='sextic37' else {'a':4,'f':4}
    exponent=tuple(mon.get(v,0) for v in e.NAMES)
    coefficient=poly.get(exponent,0)
    expected=4 if name=='sextic37' else 1
    if coefficient!=expected:raise RuntimeError('Leading coefficient failed')
    removed={x for x,_ in defs}
    variables=[v for v in e.VARS if v not in removed]
    live={v for p in eqs for m in p for v,k in zip(e.NAMES,m) if k}
    if live!=set(variables+e.PORTS):raise RuntimeError('Variable/port liveness mismatch')
    result={
       'name':name,'domain':'unrestricted integers','variables':variables,
       'variable_count':len(variables),'equation_count':len(eqs),
       'fixed_numerals':e.PORTS,'coefficient_binding':e.packet['coefficient_binding'],
       'residuals':[e.fmt(p) for p in eqs],'residual_degrees':degrees,
       'single_polynomial':'sum of squares of the listed residuals',
       'exact_degree':target_degree,
       'exact_degree_certificate':{'monomial':mon,'coefficient':coefficient},
       'unit_eliminations':history,'source_sha256':hashlib.sha256(e.SOURCE.read_bytes()).hexdigest(),
       'source_path':'57-separated-degrees/quartic/quartic45.json',
       'symbolic_residual_term_counts':[len(p) for p in eqs],
       'symbolic_sos_term_count':len(poly),
       'status':'Exact integer zero-set bijection to the pinned Q45; inherits its compiler/calibration proof boundary.'
    }
    (ROOT/(name+'.json')).write_text(json.dumps(result,indent=2)+'\n')
    return {'name':name,'variables':len(variables),'residuals':len(eqs),
            'degree':target_degree,'coefficient_certificate':result['exact_degree_certificate'],
            'sos_symbolic_terms':len(poly),'result_sha256':hashlib.sha256((ROOT/(name+'.json')).read_bytes()).hexdigest()}

def main():
    results=[canonical(DEFINITIONS_37,6,'sextic37'),canonical(DEFINITIONS_34,8,'octic34')]
    receipt={'status':'passed','source_sha256':hashlib.sha256(e.SOURCE.read_bytes()).hexdigest(),'constructions':results}
    (ROOT/'REDUCTION_VERIFICATION.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()

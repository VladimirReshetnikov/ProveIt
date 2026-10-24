#!/usr/bin/env python3
"""Materialize report.zip's twelve-positive degree-70 equation. No Lean."""
import importlib.util
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent
source=ROOT.parent/'short-unit-products/build.py'
spec=importlib.util.spec_from_file_location('carrier_builder',source)
carrier=importlib.util.module_from_spec(spec)
spec.loader.exec_module(carrier)

def build():
    dag=carrier.DAG()
    a,s,p,z=dag.add,dag.sub,dag.mul,dag.sq
    r=carrier.prefix(dag,6)
    f=a('t',1,'f');f2=z(f,'f2');rho=s(f2,1,'rho')
    Q=p(r['Delta'],rho,'Q');oneQ=s(1,Q,'oneQ');den=z(r['c2'],'den')
    V=s(p(f2,s(p(r['c'],'T'),r['R'])),r['c'],'V')
    vn=a(V,'n','vn');vn2=z(vn,'vn2')
    h=s(s(vn2,p(Q,s(vn2,z(V)))),1,'h')
    bn=p(p(2,oneQ),vn,'bn');AN=a(p(den,h),p(oneQ,Q),'AN')
    N=s(z(AN),p(p(den,Q),z(bn)),'N')
    out=s(p(p(a(r['A0'],1),a(r['A1'],1)),a(N,1)),1,'P12')
    v=['j','F','alpha','t','T','X','Y','r','eta','zeta','n','gamma']
    return dag.packet(v,out,70,'p12_ordinary_saturated',[r['A0'],r['A1'],N])

if __name__=='__main__':
    packet=build()
    (ROOT/'p12_ordinary_degree70.json').write_text(json.dumps(packet,indent=2)+'\n')
    print(packet['operations'],packet['operation_breakdown'])

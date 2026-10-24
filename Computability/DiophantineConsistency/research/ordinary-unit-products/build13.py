#!/usr/bin/env python3
"""Ordinary strong norm in the thirteen-positive unit-product family."""
import importlib.util,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('carrier_builder',ROOT.parent/'short-unit-products/build.py')
carrier=importlib.util.module_from_spec(spec);spec.loader.exec_module(carrier)
def build():
    dag=carrier.DAG();a,s,p,z=dag.add,dag.sub,dag.mul,dag.sq
    r=carrier.prefix(dag,3)
    f2=z('f','f2');rho=s(f2,1,'rho');Q=p(r['Delta'],rho,'Q')
    I=p('i',r['c2'],'I');Fs=a(s(z(I),Q),1,'Fs')
    V=s(p(f2,s(p(r['c'],'T'),r['R'])),r['c'],'V')
    y2=z(a(V,'u'),'y2');Fa=s(y2,p(Q,s(y2,z(V))),'Fa')
    F0=a(r['A0'],1,'F0');F1=a(r['A1'],1,'F1')
    out=s(p(p(p(F0,F1),Fa),Fs),1,'P13')
    vs=['j','F','alpha','f','i','T','X','Y','r','eta','zeta','u','gamma']
    return dag.packet(vs,out,51,'p13_ordinary_product',[r['A0'],r['A1'],'Fa','Fs'])
if __name__=='__main__':
    p=build();(ROOT/'p13_ordinary_degree51.json').write_text(json.dumps(p,indent=2)+'\n')
    print(p['operations'],p['operation_breakdown'])

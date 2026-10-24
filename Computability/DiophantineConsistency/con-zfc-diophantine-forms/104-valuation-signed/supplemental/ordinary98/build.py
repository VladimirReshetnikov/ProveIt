#!/usr/bin/env python3
"""An identical-polynomial evaluator for the ordinary 12-positive endpoint.

The carrier and inherited proof are from ProveIt, commit
85ae4070019efd66ea3e58e9a67d287528094e8b. Only the saturated norm schedule changes.
"""
import json
from pathlib import Path
from carrier import DAG, prefix

ROOT=Path(__file__).resolve().parent

def build(rewrite=True):
    dag=DAG()
    a,s,p,z=dag.add,dag.sub,dag.mul,dag.sq
    r=prefix(dag,6)
    f=a('t',1,'f');f2=z(f,'f2');rho=s(f2,1,'rho')
    Q=p(r['Delta'],rho,'Q');e=s(1,Q,'oneQ');den=z(r['c2'],'den')
    V=s(p(f2,s(p(r['c'],'T'),r['R'])),r['c'],'V')
    vn=a(V,'n','vn');vn2=z(vn,'vn2')
    if rewrite:
        Ea=s(p(Q,z(V)),1,'Ea')
        h=a(p(e,vn2),Ea,'h');b=p(e,Q,'b')
        AN=s(p(den,h),b,'AN')
        N=a(z(AN),p(p(p(4,den),b),Ea),'N')
    else:
        h=s(s(vn2,p(Q,s(vn2,z(V)))),1,'h')
        bn=p(p(2,e),vn,'bn');AN=a(p(den,h),p(e,Q),'AN')
        N=s(z(AN),p(p(den,Q),z(bn)),'N')
    out=s(p(p(a(r['A0'],1),a(r['A1'],1)),a(N,1)),1,'P12')
    v=['j','F','alpha','t','T','X','Y','r','eta','zeta','n','gamma']
    packet=dag.packet(v,out,70,'ordinary12_polarized' if rewrite else 'ordinary12_parent',[r['A0'],r['A1'],N])
    packet['coefficient_binding']='native/ACTIVE_BINDING.json'
    return packet

if __name__=='__main__':
    for name,rw in [('ordinary12_98.json',True),('ordinary12_parent100.json',False)]:
        packet=build(rw)
        (ROOT/name).write_text(json.dumps(packet,indent=2)+'\n')
        print(name,packet['operations'],packet['operation_breakdown'])

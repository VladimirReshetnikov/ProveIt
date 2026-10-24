#!/usr/bin/env python3
"""Centered auxiliary coordinates for fixed-blank strong-root deletion.

Only inert product67.json and our own prior builder are read. No archived
H10 emitter, power array, or Lean compiler is executed.
"""
import argparse
from collections import Counter
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent.parent
BASE=HERE.parent/'fixed-root-elimination/build.py'
spec=importlib.util.spec_from_file_location('prior_fixed_root',BASE)
base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)

def need(ok,label):
    if not ok:raise ValueError(label)

def encoded(x):return (json.dumps(x,indent=2)+'\n').encode()

def centered_normalized(parent,unit):
    p=base.candidate(parent,unit)
    prefix='unit' if unit else 'field'
    rows=[]
    for row in p['source']:
        if row[0]=='aux_y2':continue
        rows.append(row)
        if row[0]==prefix+'_b':
            rows.append([prefix+'_old_y','-','y',prefix+'_b'])
            rows.append(['aux_y2','*',prefix+'_old_y',prefix+'_old_y'])
    p.update(name='normalized_centered_'+('unit76' if unit else 'field74'),source=rows,exact_degree=263 if unit else 312,
             proof_boundary='Ordinary source/root proof in PROOF.md; old auxiliary ordinate is y-b and may have either sign; no new Lean/internal derivation.',
             cuts={'D':prefix+'_D','b':prefix+'_b','u':prefix+'_u','Q':'R16','y':'y','P':prefix+'_P'})
    return p

def ordinary(parent):
    rows,_=base.retained(parent)
    rows=[r for r in rows if r[0] not in {'aux_y2','aux_coefficient_root','R16'}]
    def emit(n,op,a,b):
        n='ordinary_'+n;rows.append([n,op,a,b]);return n
    I=emit('I','*','i','c2');Q=emit('Q','*',I,I)
    dn=emit('Dnum','+','A',Q)
    dc=emit('dc','*','A','R10a');rd=emit('RDnum','*','r_lhs',dn)
    b=emit('b','+',dc,rd)
    ts=emit('T2','*','T','T');pp=emit('p0','*','Ac2',dn);p=emit('p','*',pp,ts)
    bs=emit('b2','*',b,b)
    yn=emit('ynum','-','y',b);ys=emit('ynum2','*',yn,yn)
    ss=emit('sum','+',p,bs);gap=emit('gap','-',ss,ys)
    qgap=emit('Qgap','*',Q,gap);ap=emit('Aplus','+',qgap,ys)
    ds=emit('Delta2','*','A','A');aa=emit('A','-',ap,ds)
    qp=emit('Qp','*',Q,p);qb=emit('Qb2','*',Q,bs)
    cross=emit('cross','*',qp,qb);four=emit('four','*',4,cross)
    a2=emit('A2','*',aa,aa);kn=emit('K','-',a2,four)
    guard=emit('guard','+',kn,1)
    px=emit('P0','*','norm_pair','norm_index');prod=emit('P','*',px,'norm_transport')
    val=emit('product','*',prod,guard);out=emit('out','-',val,1)
    return {'name':'ordinary_scaled_auxiliary_center76','witness_domain':'strictly positive integers',
      'witnesses':[v for v in parent['witnesses'] if v!='f'],'fixed_numerals':parent['fixed_numerals'],
      'source':rows,'output':out,'exact_degree':191,
      'coefficient_binding':copy.deepcopy(base.candidate(parent,True)['coefficient_binding']),
      'provenance':{'parent_sha256':base.PARENT_SHA,'retained_rows':47,'new_rows':29,
        'change':'Ordinary I=i c², Q=I²; scaled auxiliary old_y=(y-bnum)/Delta, Dnum=Delta+Q, bnum=Delta*c+R*Dnum'},
      'proof_boundary':'Ordinary rational-root integrality via balanced unit reduction, then adjacent Pell saturation and inherited compact36 native calibration. No new Lean/internal derivation.',
      'cuts':{'Delta':'A','Q':Q,'b':b,'u':'u_abstract','y':'y','P':prod,'p':p,'norm':kn,'A':aa}}

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--check',action='store_true');args=parser.parse_args()
    raw=base.PARENT.read_bytes();need(hashlib.sha256(raw).hexdigest()==base.PARENT_SHA,'parent67 pin')
    parent=json.loads(raw);fixed,binding=base.fixed_values()
    summary={}
    for name,obj in [('field74',centered_normalized(parent,False)),('unit76_reference',centered_normalized(parent,True)),('ordinary76',ordinary(parent))]:
        topo=base.topology(obj);obj['operations']=topo['operations'];obj['operation_counts']=topo['operation_counts']
        expected={'field74':74,'unit76_reference':76,'ordinary76':76}[name]
        need(obj['operations']==expected,'predicted count '+name)
        data=encoded(obj);path=HERE/(name+'.json')
        if args.check:need(path.read_bytes()==data,'deterministic literal '+name)
        else:path.write_bytes(data)
        summary[name]={'sha256':hashlib.sha256(data).hexdigest(),'degree':obj['exact_degree'],**topo}
    receipt={'status':'PASS','parent_sha256':base.PARENT_SHA,'fixed_binding':binding,'circuits':summary,
      'scope':'Literal topology/count and complete fixed-port bytes; proof/degree audited separately.'}
    path=HERE/'BUILD.json';data=encoded(receipt)
    if args.check:need(path.read_bytes()==data,'deterministic BUILD')
    else:path.write_bytes(data)
    print(json.dumps(summary,indent=2))
if __name__=='__main__':main()

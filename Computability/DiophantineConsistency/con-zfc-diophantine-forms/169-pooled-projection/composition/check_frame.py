#!/usr/bin/env python3
"""Independent actual-port square-frame audit for the factorial-free composition."""
from collections import defaultdict
from pathlib import Path
import argparse,json,hashlib

def add(*ps):
    o=defaultdict(int)
    for p in ps:
        for m,c in p.items():o[m]+=c
    return {m:c for m,c in o.items() if c}
def scale(k,p):return {m:k*c for m,c in p.items() if k*c}
def multiply(p,q):
    o=defaultdict(int)
    for m,c in p.items():
        for n,d in q.items():o[tuple(sorted(m+n))]+=c*d
    return {m:c for m,c in o.items() if c}
def check(path):
    b=path.read_bytes();e=json.loads(b)
    return check_data(e,b)
def check_data(e,b=b''):
    ns={v['name']:i for i,v in enumerate(e['variables'])}
    def v(s):return {(ns[s],):1}
    def const(n):return {():n} if n else {}
    def shifted(s,n):return add(v(s),const(n))
    t=v('t0');F=v('crt.growth_majorant_F');x=v('x');q=shifted('pow2.output',-1);C=scale(2,v('crt.even_index_half'))
    atoms=[('horizon',t),('horizon+1',add(t,const(1))),('binomial_upper_index',add(F,t)),
        ('beta_code',x),('growth_base',t),('growth_output',F),('binomial_output',v('choose0.output')),
        ('beta_spacing+1',v('y')),('schema_a',shifted('crt.encoded.a',-1))]
    for s in ['b','c','d','S','Sp','u','vq']:atoms.append(('schema_'+s,v('crt.encoded.'+s)))
    atoms += [('row_index',C),('modulus_power',v('pow1.output')),('derived_label',v('add.380')),
        ('radix',q),('radix+1',v('pow2.output')),('self_radix_base',v('self_radix.BH'))]
    for k in [3,4,5,7,8,9,10,11,12,13,14,15,16,17]:atoms.append(('power_output_'+str(k),v('pow'+str(k)+'.output')))
    expected=add(v('shared.W'),const(-2),*(scale(-1,multiply(p,p)) for _,p in atoms))
    rows=[r for r in e['residuals'] if r['label']=='shared.frame_definition']
    if len(rows)!=1:raise ValueError('unique frame row')
    observed={tuple(m):c for c,m in rows[0]['terms']}
    if observed!=expected:raise ValueError(('exact square-frame identity',add(observed,scale(-1,expected))))
    indices={0:t,1:x,2:x,3:add(F,t),4:t,5:shifted('crt.encoded.a',-1),
        7:v('crt.encoded.b'),8:v('crt.encoded.c'),9:v('crt.encoded.d'),10:v('crt.encoded.S'),
        11:v('y'),12:v('crt.encoded.Sp'),13:v('crt.encoded.u'),14:x,15:v('crt.encoded.vq'),16:C,17:v('add.380')}
    bases={0:t,1:v('choose0.output'),2:v('self_radix.BH')}
    for k in [3,5,7,8,9,10,12,13,15,16,17]:bases[k]=v('pow2.output')
    for k in [4,11,14]:bases[k]=q
    outputs={k:(F if k==0 else q if k==2 else v('pow'+str(k)+'.output')) for k in indices}
    records=[];values=[p for _,p in atoms]
    for k,index in indices.items():
        item={'request':k}
        for role,p in [('base',bases[k]),('index',index),('output',outputs[k])]:
            if p not in values:raise ValueError(('missing actual frame atom',k,role))
            item[role]=[[c,list(m)] for m,c in sorted(p.items())]
        records.append(item)
    return {'status':'passed','equation_sha256':hashlib.sha256(b).hexdigest(),
        'frame_identity':'W = 2 + sum(atom^2)','atom_count':len(atoms),'request_count':len(records),
        'all_actual_bases_indices_outputs_squared_below_W':True,
        'atoms':[{'label':s,'terms':[[c,list(m)] for m,c in sorted(p.items())]} for s,p in atoms],
        'requests':records,'scope':'Exact finite identity and actual-port coverage; inherited signed-frame theorem supplies |A|>W^W.'}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('equation',type=Path);p.add_argument('--receipt',type=Path);a=p.parse_args();result=check(a.equation);s=json.dumps(result,indent=2)+'\n'
    if a.receipt:a.receipt.write_text(s)
    print(s,end='')

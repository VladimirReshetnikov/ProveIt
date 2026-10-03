#!/usr/bin/env python3
"""Paid unit top mask in three frozen complete projective sources."""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random

PINS = {'../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md': '47a2c5b69f3c87b7a1ddc61ef84757023de291b63d1330e2c8dc9b40e811ab8b', '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b', '../../1980/PELL_RELAXED_AUXILIARY_PROOF.md': '9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90', 'group_macro_automaton_sharing.json': '8e7044b66bebbacc0f89721807369607146b57bb67b14d1ddb9c4e05586a681b', 'group_macro_automaton_sharing.md': 'e253a396f999e8045bb1c4ee223602907f8ea003b7b7f3d93218cb425ffd5585', 'group_macro_automaton_sharing.py': 'f9d660c3309c030c98c8209f2b8a708a6731eedf62234d459ed4fa3f1db2af48', 'group_projective_coupled_linear_unit.md': '15fa0737a82996a8ea5c28aa62cbbe798ac5e06e4a3323c4dcaa01c9cd6286c7', 'group_projective_idle_free_paths.md': '0cc8b21be7fca0cc5763ba3862f6888f94669259ca26beb0050cd5f8ef1ec9e9', 'group_projective_joint_bound_unit.md': '3f33f4d7c04137409688b011859578924a4d1571d46d37bf1ca7ebd81a230a1e', 'group_projective_joint_first_norm.md': 'da7f6baaedaecae3166cfed050d2e913d26b280cc3332ca04bf0e8983417e9cb', 'group_projective_label_aligned_lanes.json': '232fbc5d9409da72f7f8b0335316920c93cb435bbcbb43ce122b3b8c17477008', 'group_projective_label_aligned_lanes.md': '66221327c058b335febda310bb81b656b7c7095fb4463d633f60de9cd8213edb', 'group_projective_label_aligned_lanes.py': 'cbecb51a164f7e4272a293fc2cb6e549838ec153b693399487e3ee0b4dd8c9a5', 'group_projective_output_bound_obstruction.md': 'b478f73d003a62ed530ba329c01f875be7a5da2202b746d89ccd50f8f50aa56b', 'group_projective_padded_program_margin.md': 'a4ad4487f682d250f3a9ae84cc8f4182b21d2e216fa0d53624f7368abd028952', 'group_projective_port_bias_folding.md': 'e699bb645378ced31c62dd9bb702eb6ed0ea93be8b6ee91e1cdc859b27e3c706', 'group_projective_product_radix_scale.json': '1403987d49c3613b3ca6cdc1f1794d16199af9020c9c88fd53c49981f95db9a7', 'group_projective_product_radix_scale.md': 'f342dbc1da849a7c74cc7043becad6d218582adeefffa55dec558a28b1e47b39', 'group_projective_product_radix_scale.py': 'd33e8aa3bff7559c72768be7116f0328ebad0cf65190115101457a71a0e25965', 'group_projective_reindexed_edge_geometry.md': 'ceadd45bebece376f9cbaa5e7be1740f35510a55211819376fa335ad719152d3', 'group_projective_shared_flow_target.md': '17bc108499565d3cbc5a6c55ca9395693c8fcce5c72069f5080560702424d1e4', 'group_projective_shared_flow_target.py': 'eea982ef140ac046f9fe857747fdde82a51bedc78f22306558941ab839eeacf0', 'group_projective_shared_macro_automaton.json': '284da792cce620169ebca9cae7ee77488b56fe0f68c47cf12059af5d0e980497', 'group_projective_shared_macro_automaton.md': '5933851785599c3c83bbddc28f1dbe2e43c7db17ed256a87a5dd293117bc9eb6', 'group_projective_shared_macro_automaton.py': '2cbbc82d18e0e175d3c7f44707fdc16c2bf899aaad5deafa44c0975cf0b96bf7', 'group_projective_shared_selector_pack.md': 'b29225304b4a3b96c922df5645ca7060adc60c3074ed20e561a8e074dc411d66', 'group_projective_shifted_X_quotient.md': '4f76dda46f9385a769da0c809292b466d352be2a6f2d39c5e70519bdeda37e00', 'group_projective_strong_unit_product.md': '06978175efe47f59bf497f8882b3138692abead1458c58de6a53af92b4f83605', 'group_projective_tail_quotient_shift.json': 'a422e7a65df26e626f3c36f97a53a68805b86806be3dc35d35e7d49a17b80b27', 'group_projective_tail_quotient_shift.md': 'a1e1e67df618f6f809c2e85a409509b288337f62cd1af35cfc6ca950e0efa92a', 'group_projective_tail_quotient_shift.py': '08248ad763113a6a2e60168edfd058b92be4e14b2f7932fa1be66eb406a70610', 'group_projective_zero_mortality6.md': 'c0f3cb53d8a189dd7b98e0deb892a75e64426e8ac480ee049f945ed09e896bc2', 'group_sparse_macro_flow.md': '4e4356902a52de1464c91ac5aea2a654900492b74ee252d9ea22a34e5dd6febc', 'group_sparse_macro_flow.py': '74604c1a9d1071a823e0df3388d2c89eb639cf3e088a39fa7fff3eae5113238a', 'native_controller_binary_selector56.md': '97fcdc7188f968f2ac3e315249b0e0a15dcc787c10451924ad3f2551c8bb376c'}
FACTORS = ['first_unit','selection__R15','selection__P17','index_unit',
           'linear_unit','strong_unit','joint_bound_unit']
PRIME = 1000000007


def sha(data):
    return hashlib.sha256(data).hexdigest()


def exact(a,b):
    if type(a) is not type(b): return False
    if isinstance(a,dict): return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if isinstance(a,list): return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b


def authenticate(root):
    blobs={}
    for name,pin in PINS.items():
        data=(root/name).read_bytes()
        if sha(data)!=pin: raise ValueError('Changed dependency: '+name)
        blobs[name]=data
    return blobs


def parents(blobs):
    tail=json.loads(blobs['group_projective_tail_quotient_shift.json'])['packet']
    macro=json.loads(blobs['group_projective_shared_macro_automaton.json'])['packets']
    result={'ten_letter':dict(source=tail['source'],free=['x']+tail['auxiliaries'],
                             comparisons=tail['comparisons'],exact_degree=2829)}
    for graph,p in macro.items():
        result[graph]=dict(source=p['source'],free=p['free'],comparisons=p['comparisons'],exact_degree=1789)
    return result


def rewrite(parent):
    rows=parent['source']
    assert [r for r in rows if r[0]=='range_Bminus_shift']==[
        ['range_Bminus_shift','*','range_body_scale',2]]
    assert [r[0] for r in rows if 'range_Bminus_shift' in r[2:]]==['range_M']
    assert [r for r in rows if r[0]=='range_M']==[
        ['range_M','+','range_Mbody','range_Bminus_shift']]
    new=[]
    for name,op,a,b in rows:
        if name=='range_Bminus_shift': continue
        new.append([name,op,'range_body_scale' if a=='range_Bminus_shift' else a,
                    'range_body_scale' if b=='range_Bminus_shift' else b])
    assert len(new)==len(rows)-1
    return dict(source=new,free=parent['free'][:],comparisons=parent['comparisons'],
                output='joint_outer_output')


def ledger(packet):
    free=packet['free'];rows=packet['source'];known=set(free);defs={}
    assert len(known)==len(free)
    for name,op,a,b in rows:
        assert name not in known and op in ('+','-','*')
        assert all(type(v) is int or type(v) is str and v in known for v in (a,b))
        defs[name]=(a,b);known.add(name)
    live=set();todo=['joint_outer_output']
    while todo:
        v=todo.pop()
        if type(v) is int or v in live: continue
        live.add(v);todo.extend(defs.get(v,()))
    assert live==known
    M=sum(r[1]=='*' for r in rows)
    return dict(operations=len(rows),M=M,A=len(rows)-M,positive_witnesses=len(free)-1,
                comparisons=len(packet['comparisons']),certificate_operations=len(rows)-17,
                finalizer_operations=17,all_gates_live=True)


def run(rows,values,overrides=None):
    env=dict(values)
    for name,op,a,b in rows:
        if overrides and name in overrides:
            env[name]=overrides[name];continue
        a=env[a] if type(a) is str else a;b=env[b] if type(b) is str else b
        env[name]=a*b if op=='*' else a+b if op=='+' else a-b
    return env


# Exact sparse polynomial verification of the whole folded index at H,M,Z,q cuts.
def const(n): return {():n} if n else {}
def var(s): return {(s,):1}
def add(a,b,sign=1):
    out=dict(a)
    for mon,c in b.items(): out[mon]=out.get(mon,0)+sign*c
    return {m:c for m,c in out.items() if c}
def mul(a,b):
    out={}
    for m,c in a.items():
        for n,d in b.items():
            mon=tuple(sorted(m+n));out[mon]=out.get(mon,0)+c*d
    return {m:c for m,c in out.items() if c}
def powpoly(a,n):
    out=const(1)
    for _ in range(n): out=mul(out,a)
    return out


def folded_index_proof(rows):
    defs={r[0]:r[1:] for r in rows}
    env={k:var(v) for k,v in [('range_H','H'),('range_M','M'),('range_Z','Z'),('selection__q','q')]}
    def ev(v):
        if type(v) is int: return const(v)
        if v not in env:
            op,a,b=defs[v];env[v]=mul(ev(a),ev(b)) if op=='*' else add(ev(a),ev(b),1 if op=='+' else -1)
        return env[v]
    H,M,Z,q=[var(v) for v in ('H','M','Z','q')]
    # F0=q-16H-16M+16Z-15, F1=16(H-Z)+4, F2=16(M-Z)+2, F3=16Z+8.
    fields=[add(add(add(add(q,mul(const(16),H),-1),mul(const(16),M),-1),mul(const(16),Z)),const(15),-1),
            add(mul(const(16),add(H,Z,-1)),const(4)),
            add(mul(const(16),add(M,Z,-1)),const(2)),add(mul(const(16),Z),const(8))]
    expected={}
    for i,field in enumerate(fields): expected=add(expected,mul(field,powpoly(q,i)))
    assert ev('selection__bs_packed')==expected
    assert ev('selection__F3')==fields[3]
    return len(expected)


class DAG:
    def __init__(self): self.keys={}
    def node(self,key):
        if key not in self.keys: self.keys[key]=len(self.keys)
        return self.keys[key]
    def compare(self,parent,child):
        # One shared abstract M port records the exact native-interface change;
        # all other ports/rows must literally agree, rather than assuming residuals.
        def evaluate(rows):
            env={n:self.node(('v',n)) for n in parent['free']}
            for n,op,a,b in rows:
                atom=lambda v:self.node(('c',v)) if type(v) is int else env[v]
                env[n]=self.node(('cut','M')) if n=='range_M' else self.node((op,atom(a),atom(b)))
            return env
        old,new=evaluate(parent['source']),evaluate(child['source'])
        common=set(new)-set(parent['free'])
        assert all(old[k]==new[k] for k in common)
        return len(common)


def denseop(op,a,b):
    if op=='*':
        out=[0]*(len(a)+len(b)-1)
        for i,c in enumerate(a):
            if c:
                for j,d in enumerate(b):
                    if d: out[i+j]=(out[i+j]+c*d)%PRIME
    else:
        out=[0]*max(len(a),len(b))
        for i,c in enumerate(a):out[i]=c
        for i,c in enumerate(b):out[i]=(out[i]+(c if op=='+' else -c))%PRIME
    while len(out)>1 and out[-1]==0:out.pop()
    return out


def degree_proof(packet,expected):
    rows=packet['source'];defs={r[0]:r[1:] for r in rows}
    guard={'selection__R15':['-','selection__L15','selection__Ac2'],
           'selection__L15':['*','selection__R14','selection__R14'],
           'selection__R14':['+','selection__D1','selection__gam'],
           'selection__D1':['+','selection__wn2','selection__cam2'],
           'selection__cam2':['*','selection__R10a','selection__R12'],
           'selection__A':['+','selection__a_square','selection__a4m5'],
           'selection__a_square':['*','selection__R12','selection__R12'],
           'selection__Ac2':['*','selection__A','selection__c2'],
           'selection__c2':['*','selection__R10a','selection__R10a']}
    assert all(defs[k]==v for k,v in guard.items())
    X,a,c,g,H=map(var,['X','a','c','g','H'])
    root=add(add(X,mul(a,c)),g)
    lhs=add(mul(root,root),mul(add(mul(a,a),H),mul(c,c)),-1)
    rhs=add(add(add(add(mul(X,X),mul(const(2),mul(X,mul(a,c)))),mul(const(2),mul(X,g))),mul(const(2),mul(a,mul(c,g)))),mul(g,g))
    rhs=add(rhs,mul(H,mul(c,c)),-1)
    assert lhs==rhs
    degree={n:1 for n in packet['free']};naive=dict(degree)
    dense={n:[0,i+1] for i,n in enumerate(packet['free'])}
    for name,op,a,b in rows:
        get=lambda v,d:d[v] if type(v) is str else 0
        da,db=get(a,degree),get(b,degree);na,nb=get(a,naive),get(b,naive)
        naive[name]=na+nb if op=='*' else max(na,nb)
        if name=='selection__R15':
            x,a0,c0,g,h=[degree[v] for v in ['selection__wn2','selection__R12','selection__R10a','selection__gam','selection__a4m5']]
            degree[name]=max(2*x,x+a0+c0,x+g,a0+c0+g,2*g,h+2*c0)
        else:degree[name]=da+db if op=='*' else max(da,db)
        av=dense[a] if type(a) is str else [a%PRIME];bv=dense[b] if type(b) is str else [b%PRIME]
        dense[name]=denseop(op,av,bv)
        assert len(dense[name])-1<=degree[name]
    out=packet['output'];assert degree[out]==len(dense[out])-1==expected
    assert dense[out][-1]!=0
    return dict(exact_degree=expected,guarded_upper=degree[out],naive_upper=naive[out],
                factor_degrees=[degree[n] for n in FACTORS],prime=PRIME,
                weights={n:i+1 for i,n in enumerate(packet['free'])},
                nonzero_leading_coefficient=dense[out][-1],
                full_modular_coefficients_sha256=sha(json.dumps(dense[out]).encode()))


def scalar_bounds():
    cases=[];ands=0
    for B in (16,17,32,47,64):
        for T in (1,2,16,257):
            for h,m,z in [(0,0,0),(T-1,0,T-1),(0,T-1,0),(T-1,T-1,0),(T-1,T-1,T-1)]:
                q=32*B*T;H=h+B*T;M=m+T
                fields=[q-16*H-16*M+16*z-15,16*(H-z)+4,16*(M-z)+2,16*z+8]
                assert min(fields)>0 and sum(fields)==q-1
                assert [f%16 for f in fields]==[1,4,2,8]
                r=sum(f*q**i for i,f in enumerate(fields))
                X=q*(1+(q-1)*fields[3]);Y=3*q
                assert X*Y>2*r+3 and Y*(X+1)>2*r+3
                cases.append([B,T,h,m,z])
    for B in (16,32,64):
        for T in (1,2,8,16):
            for h in range(T):
                for m in range(T):
                    z=h&m
                    assert ((h+B*T)&(m+T))==z
                    assert ((h+B*T)&(m+2*T))==z
                    ands+=1
    return dict(positive_pretyping_interfaces=len(cases),dyadic_top_AND_interfaces=ands)


def verify(root):
    blobs=authenticate(root);ps=parents(blobs);out={};counts=dict(sources=0,paid_live_gates=0,complete_register_interfaces=0,complete_evaluations=0,rational_evaluations=0,folded_index_proofs=0,full_dense_degree_proofs=0)
    rng=random.Random(243229)
    wanted={'ten_letter':(243,102,141,36),'private':(235,98,137,34),'shared':(229,97,132,33)}
    for name,parent in ps.items():
        p=rewrite(parent);l=ledger(p)
        assert (l['operations'],l['M'],l['A'],l['positive_witnesses'])==wanted[name]
        parent_ledger=ledger(parent)
        assert parent_ledger['operations']==l['operations']+1 and parent_ledger['M']==l['M']+1
        assert p['comparisons']==parent['comparisons'] and p['source'][-17:]==parent['source'][-17:]
        interface=DAG().compare(parent,p)
        assert folded_index_proof(parent['source'])==folded_index_proof(p['source'])
        # Verify every complete retained register at the changed scalar M port.
        # This is interface equality, not equal outputs at the original tuple.
        for j in range(24):
            values={n:rng.randrange(-3,5) for n in p['free']}
            if j<8:values={n:rng.randrange(1,5) for n in p['free']}
            if j>=16:values={n:Fraction(v,3) for n,v in values.items()};counts['rational_evaluations']+=1
            new=run(p['source'],values);old=run(parent['source'],values)
            ref=run(parent['source'],values,{'range_M':new['range_M']})
            assert all(new[n]==ref[n] for n,_,_,_ in p['source'])
            T=new['range_body_scale'];q=new['selection__q']
            assert new['range_M']==old['range_M']-T
            assert new['selection__bs_packed']-old['selection__bs_packed']==16*T*(1-q*q)
            assert all(new[f]==old[f] for f in FACTORS if f!='index_unit')
            assert new['index_unit']-old['index_unit']==16*T*(q*q-1)
            counts['complete_evaluations']+=1
        p['ledger']=l;p['degree_certificate']=degree_proof(p,parent['exact_degree'])
        p['parent_operations']=parent_ledger['operations'];p['interface_registers']=interface
        p['source_sha256']=sha(json.dumps(p['source'],separators=(',',':')).encode())
        out[name]=p
        counts['sources']+=1;counts['paid_live_gates']+=len(p['source']);counts['complete_register_interfaces']+=interface
        counts['folded_index_proofs']+=2;counts['full_dense_degree_proofs']+=1
    counts.update(scalar_bounds())
    return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),pins=PINS,
                packets=out,counts=counts,
                scope={'same_outer_positive_projection':True,'native_coordinates_may_change':True,
                       'same_tuple_polynomial_identity':False,'numerical_universal_bound':False,
                       'historical_Python_executed':False,'full_native_Pell_zeros_materialized':False})


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path)
    args=ap.parse_args();result=verify(args.root.resolve())
    if args.expect:assert exact(result,json.loads(args.expect.read_text())),'Exact receipt mismatch'
    encoded=json.dumps(result,sort_keys=True,indent=2)+'\n'
    assert exact(result,json.loads(encoded))
    if args.output:args.output.write_text(encoded)
    print(json.dumps({'status':'PASS','counts':result['counts']},sort_keys=True))


if __name__=='__main__':main()

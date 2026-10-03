#!/usr/bin/env python3
"""Independent three-source audit of the projective unit top mask.
Generic ring and polynomial helpers adapted from this reviewer's frozen macro review;
no author or historical Python is imported or executed.
"""
import argparse, ast, hashlib, json
from collections import Counter
from fractions import Fraction
from pathlib import Path

PINS = {'../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md': '47a2c5b69f3c87b7a1ddc61ef84757023de291b63d1330e2c8dc9b40e811ab8b', '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b', '../../1980/PELL_RELAXED_AUXILIARY_PROOF.md': '9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90', 'group_macro_automaton_sharing.json': '8e7044b66bebbacc0f89721807369607146b57bb67b14d1ddb9c4e05586a681b', 'group_macro_automaton_sharing.md': 'e253a396f999e8045bb1c4ee223602907f8ea003b7b7f3d93218cb425ffd5585', 'group_macro_automaton_sharing.py': 'f9d660c3309c030c98c8209f2b8a708a6731eedf62234d459ed4fa3f1db2af48', 'group_projective_coupled_linear_unit.md': '15fa0737a82996a8ea5c28aa62cbbe798ac5e06e4a3323c4dcaa01c9cd6286c7', 'group_projective_idle_free_paths.md': '0cc8b21be7fca0cc5763ba3862f6888f94669259ca26beb0050cd5f8ef1ec9e9', 'group_projective_joint_bound_unit.md': '3f33f4d7c04137409688b011859578924a4d1571d46d37bf1ca7ebd81a230a1e', 'group_projective_joint_first_norm.md': 'da7f6baaedaecae3166cfed050d2e913d26b280cc3332ca04bf0e8983417e9cb', 'group_projective_label_aligned_lanes.json': '232fbc5d9409da72f7f8b0335316920c93cb435bbcbb43ce122b3b8c17477008', 'group_projective_label_aligned_lanes.md': '66221327c058b335febda310bb81b656b7c7095fb4463d633f60de9cd8213edb', 'group_projective_label_aligned_lanes.py': 'cbecb51a164f7e4272a293fc2cb6e549838ec153b693399487e3ee0b4dd8c9a5', 'group_projective_output_bound_obstruction.md': 'b478f73d003a62ed530ba329c01f875be7a5da2202b746d89ccd50f8f50aa56b', 'group_projective_padded_program_margin.md': 'a4ad4487f682d250f3a9ae84cc8f4182b21d2e216fa0d53624f7368abd028952', 'group_projective_port_bias_folding.md': 'e699bb645378ced31c62dd9bb702eb6ed0ea93be8b6ee91e1cdc859b27e3c706', 'group_projective_product_radix_scale.json': '1403987d49c3613b3ca6cdc1f1794d16199af9020c9c88fd53c49981f95db9a7', 'group_projective_product_radix_scale.md': 'f342dbc1da849a7c74cc7043becad6d218582adeefffa55dec558a28b1e47b39', 'group_projective_product_radix_scale.py': 'd33e8aa3bff7559c72768be7116f0328ebad0cf65190115101457a71a0e25965', 'group_projective_reindexed_edge_geometry.md': 'ceadd45bebece376f9cbaa5e7be1740f35510a55211819376fa335ad719152d3', 'group_projective_shared_flow_target.md': '17bc108499565d3cbc5a6c55ca9395693c8fcce5c72069f5080560702424d1e4', 'group_projective_shared_flow_target.py': 'eea982ef140ac046f9fe857747fdde82a51bedc78f22306558941ab839eeacf0', 'group_projective_shared_macro_automaton.json': '284da792cce620169ebca9cae7ee77488b56fe0f68c47cf12059af5d0e980497', 'group_projective_shared_macro_automaton.md': '5933851785599c3c83bbddc28f1dbe2e43c7db17ed256a87a5dd293117bc9eb6', 'group_projective_shared_macro_automaton.py': '2cbbc82d18e0e175d3c7f44707fdc16c2bf899aaad5deafa44c0975cf0b96bf7', 'group_projective_shared_selector_pack.md': 'b29225304b4a3b96c922df5645ca7060adc60c3074ed20e561a8e074dc411d66', 'group_projective_shifted_X_quotient.md': '4f76dda46f9385a769da0c809292b466d352be2a6f2d39c5e70519bdeda37e00', 'group_projective_strong_unit_product.md': '06978175efe47f59bf497f8882b3138692abead1458c58de6a53af92b4f83605', 'group_projective_tail_quotient_shift.json': 'a422e7a65df26e626f3c36f97a53a68805b86806be3dc35d35e7d49a17b80b27', 'group_projective_tail_quotient_shift.md': 'a1e1e67df618f6f809c2e85a409509b288337f62cd1af35cfc6ca950e0efa92a', 'group_projective_tail_quotient_shift.py': '08248ad763113a6a2e60168edfd058b92be4e14b2f7932fa1be66eb406a70610', 'group_projective_zero_mortality6.md': 'c0f3cb53d8a189dd7b98e0deb892a75e64426e8ac480ee049f945ed09e896bc2', 'group_sparse_macro_flow.md': '4e4356902a52de1464c91ac5aea2a654900492b74ee252d9ea22a34e5dd6febc', 'group_sparse_macro_flow.py': '74604c1a9d1071a823e0df3388d2c89eb639cf3e088a39fa7fff3eae5113238a', 'native_controller_binary_selector56.md': '97fcdc7188f968f2ac3e315249b0e0a15dcc787c10451924ad3f2551c8bb376c'}
AUTHOR = {'group_projective_unit_top_mask.py': '1b96e1908e35f95598230c658d42d83d83cb24dc1dea48726f948353011738d3', 'group_projective_unit_top_mask.json': 'a7544f40ce74ee67088fbfa1d753a04cf921cac6f04486dd7f6d83a39befa2e2', 'group_projective_unit_top_mask.md': 'e0898d1fc20f2f4c1abff21d33f90382aeac4f6b24c648624f0e54d59a3619b2'}
FACTORS=['first_unit','selection__R15','selection__P17','index_unit','linear_unit','strong_unit','joint_bound_unit']
PRIME=1000000007

def sha(b): return hashlib.sha256(b).hexdigest()

def stable(v): return json.dumps(v, sort_keys=True, separators=(',', ':')).encode()

def poly(v): return {(v,): 1} if type(v) is str else ({(): v} if v else {})

def add(a,b,sgn=1):
    z=dict(a)
    for m,c in b.items(): z[m]=z.get(m,0)+sgn*c
    return {m:c for m,c in z.items() if c}

def mul(a,b):
    z={}
    for m,c in a.items():
        for n,d in b.items():
            k=tuple(sorted(m+n));z[k]=z.get(k,0)+c*d
    return {m:c for m,c in z.items() if c}

def ppow(a,n):
    z={():1}
    for _ in range(n): z=mul(z,a)
    return z

def pop(op,a,b): return mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)

class RingDAG:
    """Canonical affine sums and commutative products, without large expansion."""
    def __init__(self): self.nodes=[];self.ids={}
    def node(self,n):
        if n not in self.ids: self.ids[n]=len(self.nodes);self.nodes.append(n)
        return self.ids[n]
    def constant(self,n): return self.node(('C',n))
    def atom(self,n): return self.node(('V',n))
    def operation(self,op,x,y):
        if op!='*':
            terms=Counter();constant=0
            for z,sign in ((x,1),(y,1 if op=='+' else -1)):
                node=self.nodes[z]
                if node[0]=='C':constant+=sign*node[1]
                elif node[0]=='S':
                    constant+=sign*node[1]
                    for a,c in node[2]:terms[a]+=sign*c
                else:terms[z]+=sign
            terms=tuple(sorted((a,c)for a,c in terms.items()if c))
            if not terms:return self.constant(constant)
            if constant==0 and len(terms)==1 and terms[0][1]==1:return terms[0][0]
            return self.node(('S',constant,terms))
        coefficient=1;factors=[]
        for z in (x,y):
            node=self.nodes[z]
            if node[0]=='C':coefficient*=node[1]
            elif node[0]=='M':coefficient*=node[1];factors.extend(node[2])
            else:factors.append(z)
        if coefficient==0:return self.constant(0)
        if not factors:return self.constant(coefficient)
        if coefficient==1 and len(factors)==1:return factors[0]
        return self.node(('M',coefficient,tuple(sorted(factors))))

def literal_ledger(packet):
    rows=packet['source'];free=packet['free'];out='joint_outer_output'
    defs={};seen=set(free);deg={k:1 for k in free}
    for name,op,a,b in rows:
        assert name not in seen and op in ('+','-','*')
        assert all(type(v)is int or type(v)is str and v in seen for v in(a,b))
        deg[name]=sum(deg[v]if type(v)is str else 0 for v in(a,b)) if op=='*' else max(deg[v]if type(v)is str else 0 for v in(a,b))
        defs[name]=(op,a,b);seen.add(name)
    live=set();inputs=set();todo=[out]
    while todo:
        v=todo.pop()
        if type(v)is int:continue
        if v not in defs: inputs.add(v)
        elif v not in live:live.add(v);todo.extend(defs[v][1:])
    assert live==set(defs) and inputs==set(free)
    M=sum(r[1]=='*'for r in rows)
    return {'operations':len(rows),'M':M,'A':len(rows)-M,'witnesses':len(free)-1,'naive_degree_upper':deg[out]}

def dense_op(op,a,b):
    if op=='*':
        z=[0]*(len(a)+len(b)-1)
        for i,c in enumerate(a):
            if c:
                for j,d in enumerate(b):
                    if d:z[i+j]=(z[i+j]+c*d)%PRIME
    else:
        z=[0]*max(len(a),len(b))
        for i,c in enumerate(a):z[i]=c
        for i,c in enumerate(b):z[i]=(z[i]+(c if op=='+' else -c))%PRIME
    while len(z)>1 and z[-1]==0:z.pop()
    return z

def same(a,b):
    if type(a)is not type(b):return False
    if isinstance(a,dict):return a.keys()==b.keys() and all(same(a[k],b[k])for k in a)
    if isinstance(a,list):return len(a)==len(b)and all(same(x,y)for x,y in zip(a,b))
    return a==b

def authenticate(root,author_root):
    blobs={}
    for key,pin in PINS.items():
        b=(root/key).read_bytes()
        if sha(b)!=pin:raise ValueError('Changed dependency: '+key)
        blobs[key]=b
    for key,pin in AUTHOR.items():
        b=(author_root/key).read_bytes()
        if sha(b)!=pin:raise ValueError('Changed author artifact: '+key)
        blobs[key]=b
    # Inspect literals only; no imported module or executable source evaluation.
    tree=ast.parse(blobs['group_projective_unit_top_mask.py'])
    declared=next(ast.literal_eval(n.value)for n in tree.body if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='PINS'for t in n.targets))
    assert same(declared,PINS)
    rec=json.loads(blobs['group_projective_unit_top_mask.json'])
    assert same(rec['pins'],PINS)
    assert rec['source_sha256']==AUTHOR['group_projective_unit_top_mask.py']
    return blobs,rec

def main_norm_identity(rows):
    defs={r[0]:r[1:]for r in rows}
    shape={
      'selection__R15':['-','selection__L15','selection__Ac2'],
      'selection__L15':['*','selection__R14','selection__R14'],
      'selection__R14':['+','selection__D1','selection__gam'],
      'selection__D1':['+','selection__wn2','selection__cam2'],
      'selection__cam2':['*','selection__R10a','selection__R12'],
      'selection__A':['+','selection__a_square','selection__a4m5'],
      'selection__a_square':['*','selection__R12','selection__R12'],
      'selection__Ac2':['*','selection__A','selection__c2'],
      'selection__c2':['*','selection__R10a','selection__R10a']}
    assert all(defs[k]==v for k,v in shape.items())
    x,a,c,g,h=map(poly,('X','a','c','g','H'))
    root=add(add(x,mul(a,c)),g)
    old=add(mul(root,root),mul(add(mul(a,a),h),mul(c,c)),-1)
    new={}
    for coeff,mon in [(1,['X','X']),(2,['X','a','c']),(2,['X','g']),(2,['a','c','g']),(1,['g','g']),(-1,['H','c','c'])]:
        term=poly(coeff)
        for v in mon:term=mul(term,poly(v))
        new=add(new,term)
    assert old==new

def symbolic_index(rows,mask):
    defs={r[0]:r[1:]for r in rows}
    env={'range_H':poly('H'),'range_M':mask,'range_Z':poly('Z'),'selection__q':poly('q')}
    def ev(v):
        if type(v)is int:return poly(v)
        if v not in env:
            op,a,b=defs[v];env[v]=pop(op,ev(a),ev(b))
        return env[v]
    h,z,q=map(poly,('H','Z','q'))
    fields=[add(add(add(add(q,mul(poly(16),h),-1),mul(poly(16),mask),-1),mul(poly(16),z)),poly(15),-1),
            add(mul(poly(16),add(h,z,-1)),poly(4)),
            add(mul(poly(16),add(mask,z,-1)),poly(2)),add(mul(poly(16),z),poly(8))]
    expected={}
    for i,f in enumerate(fields):expected=add(expected,mul(f,ppow(q,i)))
    assert ev('selection__bs_packed')==expected
    assert ev('selection__F3')==fields[3]
    assert add(add(fields[0],fields[1]),add(fields[2],fields[3]))==add(q,poly(1),-1)
    return expected,fields

def ring_engines(parent,child,cut):
    ring=RingDAG()
    def ev_packet(p):
        env={n:ring.atom(n)for n in p['free']}
        for n,op,a,b in p['source']:
            at=lambda v:ring.constant(v)if type(v)is int else env[v]
            env[n]=ring.atom('changed-M-interface')if cut and n=='range_M'else ring.operation(op,at(a),at(b))
        return env
    return ring,ev_packet(parent),ev_packet(child)

def finalizer_identity(packet):
    defs={r[0]:r[1:]for r in packet['source']}
    env={v:poly('U'+str(i))for i,v in enumerate(FACTORS)}
    rows=[pair for i,pair in enumerate(packet['comparisons'])if i!=4]
    for i,(a,b)in enumerate(rows):
        for k,v in enumerate((a,b)):
            assert type(v)is str and v not in env
            env[v]=poly('R'+str(i)+'_'+str(k))
    def ev(v):
        if type(v)is int:return poly(v)
        if v not in env:
            op,a,b=defs[v];env[v]=pop(op,ev(a),ev(b))
        return env[v]
    units=poly(1)
    for i in range(7):units=mul(units,poly('U'+str(i)))
    sos=poly(1)
    for i in range(5):sos=add(sos,ppow(add(poly('R'+str(i)+'_0'),poly('R'+str(i)+'_1'),-1),2))
    assert ev('joint_outer_output')==add(mul(units,sos),poly(1),-1)
    # Independently expand the complete finalizer correction after index change.
    du=mul(poly(16),mul(poly('T'),add(ppow(poly('q'),2),poly(1),-1)))
    rest=poly(1)
    for i in range(7):
        if i!=3:rest=mul(rest,poly('U'+str(i)))
    new=add(mul(mul(rest,add(poly('U3'),du)),sos),poly(1),-1)
    assert add(new,ev('joint_outer_output'),-1)==mul(mul(rest,du),sos)
    return len(ev('joint_outer_output'))

def degree_check(packet,expected):
    main_norm_identity(packet['source'])
    upper={n:1 for n in packet['free']};curves={n:[0,1]for n in packet['free']}
    for n,op,a,b in packet['source']:
        da=upper[a]if type(a)is str else 0;db=upper[b]if type(b)is str else 0
        if n=='selection__R15':
            X,A,C,G,H=[upper[k]for k in ('selection__wn2','selection__R12','selection__R10a','selection__gam','selection__a4m5')]
            upper[n]=max(2*X,X+A+C,X+G,A+C+G,2*G,H+2*C)
        else:upper[n]=da+db if op=='*'else max(da,db)
        av=curves[a]if type(a)is str else[a%PRIME]
        bv=curves[b]if type(b)is str else[b%PRIME]
        curves[n]=dense_op(op,av,bv)
        assert len(curves[n])-1<=upper[n]
    out='joint_outer_output'
    assert upper[out]==expected==len(curves[out])-1
    assert [len(curves[f])-1 for f in FACTORS]==[upper[f]for f in FACTORS]
    assert upper['range_body_scale']+2*upper['selection__q']<upper['selection__bs_packed']<upper['index_unit']
    return dict(exact_degree=expected,factor_degrees=[upper[f]for f in FACTORS],
        all_coordinates='t',prime=PRIME,nonzero_leading_coefficient=curves[out][-1],
        dense_coefficients_sha256=sha(stable(curves[out])),
        correction_degree=upper['range_body_scale']+2*upper['selection__q'],
        packed_index_degree=upper['selection__bs_packed'],native_index_degree=upper['index_unit'],
        complete_correction_degree=expected-upper['index_unit']+upper['range_body_scale']+2*upper['selection__q'])

def evaluate(packet,values):
    env=dict(values)
    for n,op,a,b in packet['source']:
        av=env[a]if type(a)is str else a;bv=env[b]if type(b)is str else b
        env[n]=av*bv if op=='*'else av+bv if op=='+'else av-bv
    return env

def scalar_check():
    # Small full cubes, not the author's corner list; B need not be dyadic.
    scalar=0;bits=0;negative_index=0
    for B in (16,19,31,48):
        for T in (1,3,5):
            for h in range(T):
                for m in range(T):
                    for z in range(T):
                        H=h+B*T;M=m+T;Q=2*B*T;q=16*Q
                        assert H-z>=(B-1)*T+1
                        assert M-z>=1
                        assert Q-H-M+z>=(B-3)*T+2
                        fs=[16*(Q-H-M+z)-15,16*(H-z)+4,16*(M-z)+2,16*z+8]
                        assert min(fs)>0 and sum(fs)==q-1 and [f%16 for f in fs]==[1,4,2,8]
                        r=sum(f*q**i for i,f in enumerate(fs));X=q*(1+(q-1)*fs[3]);Y=3*q
                        assert q**3+q*q+q+1<=r<q**4 and r<q**3*(fs[3]+1)and r%16==1
                        assert X*Y>2*r+3 and Y*(X+1)>2*r+3
                        for sign in (-1,1):
                            K=r+sign
                            assert 0<K<X*Y
                            for lin in (-1,1):assert 0<2*K-lin<=2*r+3<X*Y
                        scalar+=1
    for B in (16,32,48,80):
        for T in (1,2,4,8):
            for h in range(T):
                for m in range(T):
                    assert ((h+B*T)&(m+T))==h&m
                    assert ((h+B*T)&(m+2*T))==h&m
                    bits+=1
    # Source-independent negative-index population step at every r=1 mod16.
    for r in range(17,16385,16):
        v=((r-1)&-(r-1)).bit_length()-1
        assert (r-2).bit_count()==r.bit_count()+v-2>=r.bit_count()+2
        negative_index+=1
    return dict(scalar_cubes=scalar,dyadic_block_pairs=bits,negative_index_population_identities=negative_index)

def verify(root,author_root):
    blobs,author=authenticate(root,author_root)
    t=json.loads(blobs['group_projective_tail_quotient_shift.json'])['packet']
    ps={'ten_letter':dict(source=t['source'],free=['x']+t['auxiliaries'],comparisons=t['comparisons'])}
    ps.update(json.loads(blobs['group_projective_shared_macro_automaton.json'])['packets'])
    expected={'ten_letter':(243,102,141,36,2829),'private':(235,98,137,34,1789),'shared':(229,97,132,33,1789)}
    results={};counts=dict(complete_sources=0,paid_live_gates=0,changed_interface_registers=0,unchanged_factors=0,unchanged_outer_residuals=0,whole_finalizer_proofs=0,comparisons=0,numeric_full_corrections=0,rational_full_corrections=0,dense_degree_proofs=0)
    for key,parent in ps.items():
        child=author['packets'][key];rows=parent['source']
        assert [r for r in rows if r[0]=='range_Bminus_shift']==[['range_Bminus_shift','*','range_body_scale',2]]
        assert [r[0]for r in rows if 'range_Bminus_shift'in r[2:]]==['range_M']
        assert [r for r in rows if r[0]=='range_M']==[['range_M','+','range_Mbody','range_Bminus_shift']]
        independently=[]
        for n,op,a,b in rows:
            if n=='range_Bminus_shift':continue
            independently.append([n,op,a,'range_body_scale'if n=='range_M'else b])
        assert same(independently,child['source'])
        assert same(parent['free'],child['free'])and same(parent['comparisons'],child['comparisons'])
        assert child['comparisons'][4]==['eight_units',1]
        assert same(parent['source'][-17:],child['source'][-17:])
        ld=literal_ledger(child);oldld=literal_ledger(parent)
        n,m,a,w,d=expected[key]
        assert (ld['operations'],ld['M'],ld['A'],ld['witnesses'])==(n,m,a,w)
        assert oldld['operations']==n+1 and oldld['M']==m+1 and oldld['A']==a
        assert child['ledger']['operations']==n and child['ledger']['M']==m and child['ledger']['A']==a
        assert child['ledger']['positive_witnesses']==w and child['ledger']['certificate_operations']==n-17
        assert child['ledger']['comparisons']==6 and child['ledger']['finalizer_operations']==17
        ring,old,new=ring_engines(parent,child,True)
        assert all(old[v]==new[v]for v,_,_,_ in child['source'])
        counts['changed_interface_registers']+=n
        ring,old,new=ring_engines(parent,child,False)
        assert all(old[v]==new[v]for v in FACTORS if v!='index_unit')
        assert old['index_unit']!=new['index_unit']
        for i,(a0,b0)in enumerate(child['comparisons']):
            if i!=4:assert ring.operation('-',old[a0],old[b0])==ring.operation('-',new[a0],new[b0])
        for v in ('selection__q','selection__F3','selection__wn2','range_H','range_Z'):
            assert old[v]==new[v]
        oldidx,oldfs=symbolic_index(parent['source'],poly('M'))
        newidx,newfs=symbolic_index(child['source'],add(poly('M'),poly('T'),-1))
        shift=mul(poly(16),mul(poly('T'),add(poly(1),ppow(poly('q'),2),-1)))
        assert add(newidx,oldidx,-1)==shift
        assert add(newfs[0],oldfs[0],-1)==mul(poly(16),poly('T'))
        assert add(newfs[2],oldfs[2],-1)==mul(poly(-16),poly('T'))
        for i in (1,3):assert newfs[i]==oldfs[i]
        terms=finalizer_identity(child);assert terms==finalizer_identity(parent)
        deg=degree_check(child,d)
        assert same(deg['factor_degrees'],child['degree_certificate']['factor_degrees'])
        assert child['degree_certificate']['exact_degree']==d
        for seed in range(12):
            values={v:((i+3)*(seed+5)%7)-3 for i,v in enumerate(child['free'])}
            if seed>=8:values={v:Fraction(x,2+(seed%3))for v,x in values.items()}
            e0=evaluate(parent,values);e1=evaluate(child,values)
            change=16*e1['range_body_scale']*(e1['selection__q']**2-1)
            rest=1
            for f in FACTORS:
                if f!='index_unit':assert e0[f]==e1[f];rest*=e1[f]
            outer=1+sum((e1[a0]-e1[b0])**2 for i,(a0,b0)in enumerate(child['comparisons'])if i!=4)
            assert e1['index_unit']-e0['index_unit']==change
            assert e1['joint_outer_output']-e0['joint_outer_output']==change*rest*outer
            counts['numeric_full_corrections']+=1
            if seed>=8:counts['rational_full_corrections']+=1
        results[key]=dict(ledger=ld,certificate_M=m-6,certificate_A=a-11,source_sha256=sha(stable(child['source'])),degree=deg,finalizer_monomials_at_free_factor_and_outer_ports=terms)
        counts['complete_sources']+=1;counts['paid_live_gates']+=n;counts['unchanged_factors']+=6;counts['unchanged_outer_residuals']+=5;counts['whole_finalizer_proofs']+=2;counts['comparisons']+=6;counts['dense_degree_proofs']+=1
    counts.update(scalar_check())
    return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),author_pins=AUTHOR,dependency_pins=PINS,counts=counts,results=results,
        scope=dict(full_saved_sources=3,historical_or_author_Python_executed=False,full_positive_zero_projection_proof='companion note; inherited prescribed-native converse',same_tuple_polynomial_identity=False,positive_native_tuple_bijection=False,full_native_Pell_zeros_materialized=False,new_numerical_universal_bound=False))

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',required=True,type=Path);ap.add_argument('--author-root',type=Path);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path)
    args=ap.parse_args();root=args.root.resolve();result=verify(root,(args.author_root or root).resolve())
    data=json.dumps(result,sort_keys=True,indent=2)+'\n';assert same(result,json.loads(data))
    if args.expect:assert same(result,json.loads(args.expect.read_text())),'Receipt mismatch'
    if args.output:args.output.write_text(data)
    print(json.dumps(dict(status='PASS',counts=result['counts']),sort_keys=True))
if __name__=='__main__':main()

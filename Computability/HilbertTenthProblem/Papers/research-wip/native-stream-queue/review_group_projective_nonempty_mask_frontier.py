#!/usr/bin/env python3
"""Independent full-source review of the two nonempty projective mask charts.
Ring/polynomial helpers reused from this reviewer's top-mask audit; no author
or historical Python is imported or executed.
"""
import argparse, ast, hashlib, json
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__:
    raise RuntimeError("This reviewer requires assertions; optimized Python is unsupported")
PINS={'group_macro_automaton_sharing.py': 'f9d660c3309c030c98c8209f2b8a708a6731eedf62234d459ed4fa3f1db2af48', 'group_macro_automaton_sharing.json': '8e7044b66bebbacc0f89721807369607146b57bb67b14d1ddb9c4e05586a681b', 'group_macro_automaton_sharing.md': 'e253a396f999e8045bb1c4ee223602907f8ea003b7b7f3d93218cb425ffd5585', 'group_projective_label_aligned_lanes.py': 'cbecb51a164f7e4272a293fc2cb6e549838ec153b693399487e3ee0b4dd8c9a5', 'group_projective_label_aligned_lanes.json': '232fbc5d9409da72f7f8b0335316920c93cb435bbcbb43ce122b3b8c17477008', 'group_projective_label_aligned_lanes.md': '66221327c058b335febda310bb81b656b7c7095fb4463d633f60de9cd8213edb', 'group_projective_tail_quotient_shift.py': '08248ad763113a6a2e60168edfd058b92be4e14b2f7932fa1be66eb406a70610', 'group_projective_tail_quotient_shift.json': 'a422e7a65df26e626f3c36f97a53a68805b86806be3dc35d35e7d49a17b80b27', 'group_projective_tail_quotient_shift.md': 'a1e1e67df618f6f809c2e85a409509b288337f62cd1af35cfc6ca950e0efa92a', 'group_projective_idle_free_paths.md': '0cc8b21be7fca0cc5763ba3862f6888f94669259ca26beb0050cd5f8ef1ec9e9', 'group_projective_reindexed_edge_geometry.md': 'ceadd45bebece376f9cbaa5e7be1740f35510a55211819376fa335ad719152d3', 'group_sparse_macro_flow.py': '74604c1a9d1071a823e0df3388d2c89eb639cf3e088a39fa7fff3eae5113238a', 'group_sparse_macro_flow.md': '4e4356902a52de1464c91ac5aea2a654900492b74ee252d9ea22a34e5dd6febc', 'group_projective_shared_flow_target.py': 'eea982ef140ac046f9fe857747fdde82a51bedc78f22306558941ab839eeacf0', 'group_projective_shared_flow_target.md': '17bc108499565d3cbc5a6c55ca9395693c8fcce5c72069f5080560702424d1e4', 'group_projective_shared_selector_pack.md': 'b29225304b4a3b96c922df5645ca7060adc60c3074ed20e561a8e074dc411d66', 'group_projective_port_bias_folding.md': 'e699bb645378ced31c62dd9bb702eb6ed0ea93be8b6ee91e1cdc859b27e3c706', 'group_projective_zero_mortality6.md': 'c0f3cb53d8a189dd7b98e0deb892a75e64426e8ac480ee049f945ed09e896bc2', '../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md': '47a2c5b69f3c87b7a1ddc61ef84757023de291b63d1330e2c8dc9b40e811ab8b', '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b', '../../1980/PELL_RELAXED_AUXILIARY_PROOF.md': '9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90', 'group_projective_coupled_linear_unit.md': '15fa0737a82996a8ea5c28aa62cbbe798ac5e06e4a3323c4dcaa01c9cd6286c7', 'group_projective_joint_bound_unit.md': '3f33f4d7c04137409688b011859578924a4d1571d46d37bf1ca7ebd81a230a1e', 'group_projective_joint_first_norm.md': 'da7f6baaedaecae3166cfed050d2e913d26b280cc3332ca04bf0e8983417e9cb', 'group_projective_output_bound_obstruction.md': 'b478f73d003a62ed530ba329c01f875be7a5da2202b746d89ccd50f8f50aa56b', 'group_projective_padded_program_margin.md': 'a4ad4487f682d250f3a9ae84cc8f4182b21d2e216fa0d53624f7368abd028952', 'group_projective_product_radix_scale.json': '1403987d49c3613b3ca6cdc1f1794d16199af9020c9c88fd53c49981f95db9a7', 'group_projective_product_radix_scale.md': 'f342dbc1da849a7c74cc7043becad6d218582adeefffa55dec558a28b1e47b39', 'group_projective_product_radix_scale.py': 'd33e8aa3bff7559c72768be7116f0328ebad0cf65190115101457a71a0e25965', 'group_projective_shifted_X_quotient.md': '4f76dda46f9385a769da0c809292b466d352be2a6f2d39c5e70519bdeda37e00', 'group_projective_strong_unit_product.md': '06978175efe47f59bf497f8882b3138692abead1458c58de6a53af92b4f83605', 'native_controller_binary_selector56.md': '97fcdc7188f968f2ac3e315249b0e0a15dcc787c10451924ad3f2551c8bb376c', 'group_projective_shared_macro_automaton.json': '284da792cce620169ebca9cae7ee77488b56fe0f68c47cf12059af5d0e980497', 'group_projective_shared_macro_automaton.md': '5933851785599c3c83bbddc28f1dbe2e43c7db17ed256a87a5dd293117bc9eb6', 'group_projective_shared_macro_automaton.py': '2cbbc82d18e0e175d3c7f44707fdc16c2bf899aaad5deafa44c0975cf0b96bf7', 'group_projective_inverse_macro_sharing.py': 'c23f1cff1ccf1d7ad004c29670cf08926e05790eb02baeaddf4c691bd9b02957', 'group_projective_inverse_macro_sharing.json': '4f02c041fcb8db78849c5d95c2b23cabab615c88e42ef648f9c8377d876fb09b', 'group_projective_inverse_macro_sharing.md': '8ba6acdfcbf932c2814b44de590ac456ae223d7d686d19d72d54e17e2e0c8ac0', 'group_projective_unit_top_mask.py': '1b96e1908e35f95598230c658d42d83d83cb24dc1dea48726f948353011738d3', 'group_projective_unit_top_mask.json': 'a7544f40ce74ee67088fbfa1d753a04cf921cac6f04486dd7f6d83a39befa2e2', 'group_projective_unit_top_mask.md': 'e0898d1fc20f2f4c1abff21d33f90382aeac4f6b24c648624f0e54d59a3619b2'}
AUTHOR={'group_projective_nonempty_mask_frontier.py': '10d38ebaeac82c9e8ba39eefac3d03a9092e08035a8b5f0aef8dd30f78992cd5', 'group_projective_nonempty_mask_frontier.json': '589337541f83814e8d546d919caf2ab4a8977b76583f0110b9509e812521b655', 'group_projective_nonempty_mask_frontier.md': 'a0baff1b8223955f7d7682f31f8a8d1d62abe5bf72bce251e750207937fbce54'}
FACTORS=['first_unit','selection__R15','selection__P17','index_unit','linear_unit','strong_unit','joint_bound_unit']
PRIME=1000000007
P='controller__geometry_power'

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

def evaluate(packet,values):
    env=dict(values)
    for n,op,a,b in packet['source']:
        av=env[a]if type(a)is str else a;bv=env[b]if type(b)is str else b
        env[n]=av*bv if op=='*'else av+bv if op=='+'else av-bv
    return env

def authenticate(root,author_root):
    assert len(AUTHOR)==3,'Freeze author trio before replay'
    blobs={}
    for name,pin in PINS.items():
        b=(root/name).read_bytes()
        if sha(b)!=pin:raise ValueError('Changed dependency: '+name)
        blobs[name]=b
    for name,pin in AUTHOR.items():
        b=(author_root/name).read_bytes()
        if sha(b)!=pin:raise ValueError('Changed author artifact: '+name)
        blobs[name]=b
    source=blobs['group_projective_nonempty_mask_frontier.py'];tree=ast.parse(source)
    declared=next(ast.literal_eval(n.value)for n in tree.body if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='PINS'for t in n.targets))
    assert same(PINS,declared)
    receipt=json.loads(blobs['group_projective_nonempty_mask_frontier.json'])
    assert same(receipt['pins'],PINS)and receipt['source_sha256']==sha(source)
    return blobs,receipt

def polynomial_evaluator(packet,cuts):
    defs={r[0]:r[1:]for r in packet['source']};cache=dict(cuts)
    def ev(v):
        if type(v)is int:return poly(v)
        if v not in cache:
            if v not in defs:cache[v]=poly(v)
            else:
                op,a,b=defs[v];cache[v]=pop(op,ev(a),ev(b))
        return cache[v]
    return ev

def graph_cuts(p):
    ev=polynomial_evaluator(p,{P:poly('P'),'B':poly('B')})
    expected={v:{}for v in ('computed_J','controller__edge_word','controller__flow_left','controller__flow_right','physical_Sbatch','history__dS0','history__dS1','history__dS2','history__dS3')}
    assert len(p['edges'])==28 and len(p['positions'])==28 and len(set(p['positions']))==28
    for i,((a,b,label),pos)in enumerate(zip(p['edges'],p['positions'])):
        assert 0<=a<32 and 0<=b<32 and 1<=label<=8 and 0<=pos<32
        f=add(poly('controller__edge_hat'+str(i+1)),poly(1),-1)
        expected['computed_J']=add(expected['computed_J'],f)
        expected['controller__edge_word']=add(expected['controller__edge_word'],mul(f,ppow(poly('P'),pos)))
        expected['physical_Sbatch']=add(expected['physical_Sbatch'],mul(f,ppow(poly('P'),label-1)))
        expected['controller__flow_left']=add(expected['controller__flow_left'],mul(poly(a),f))
        expected['controller__flow_right']=add(expected['controller__flow_right'],mul(poly(b),mul(poly('B'),f)))
        key='history__dS'+str((label-1)//2);expected[key]=add(expected[key],f,1 if label%2 else -1)
    rep={}
    for i in range(32):rep=add(rep,ppow(poly('P'),i))
    expected['controller__origin_mask']=mul(expected['computed_J'],rep)
    expected['joint_scale']=ppow(poly('P'),40)
    expected['range_body_scale']=ppow(poly('P'),p['a_scale'])
    assert set(expected)==set(p['cuts'])
    for name,want in expected.items():assert ev(p['cuts'][name])==want,name
    return dict(polynomials=len(expected),coefficient_terms=sum(map(len,expected.values())))

def joined_cuts(p):
    cuts={P:poly('p'),p['cuts']['computed_J']:poly('j'),'B':poly('b'),'D':poly('d'),
          'selection__Hbatch':poly('h'),'selection__Mbatch':poly('m'),'selection__Zbatch':poly('z'),p['cuts']['controller__edge_word']:poly('c')}
    ev=polynomial_evaluator(p,cuts);v={k:poly(k)for k in 'pjbdhmzc'}
    power=lambda i:ppow(v['p'],i)
    def rep(n):
        out={}
        for i in range(n):out=add(out,power(i))
        return out
    def plus(*args):
        out={}
        for a in args:out=add(out,a)
        return out
    origin=mul(v['j'],rep(32));R=mul(v['j'],rep(p['range_lanes']));T=power(40);T2=power(p['a_scale'])
    mask=mul(add(mul(poly(2),v['d']),poly(1),-1),R)
    H0=plus(v['h'],mul(power(8),v['c']),mul(T,v['h']))
    M0=plus(v['m'],mul(power(8),origin),mul(T,mask))
    Z=plus(v['z'],mul(power(8),v['c']),mul(T,v['h']))
    wanted={'controller__lane_repunit2':rep(8),'controller__flow_184':rep(32),
            'controller__lane_power3':power(8),'controller__flow_185':power(32),
            'controller__origin_mask':origin,'joint_scale':T,'range_body_scale':T2,
            'range_cell':add(mul(poly(2),v['d']),poly(1),-1),'range_mask8':mask,
            'range_Hbody':H0,'range_Mbody':M0,'range_H':plus(H0,mul(v['b'],T2)),
            'range_M':plus(M0,T2),'range_Z':Z,'selection__q':mul(poly(32),mul(v['b'],T2))}
    if p['range_lanes']==8:wanted['range_origin8']=R
    for name,want in wanted.items():assert ev(name)==want,name
    return dict(polynomials=len(wanted),coefficient_terms=sum(map(len,wanted.values())))

def interface_proof(parent,child):
    ring=RingDAG();cuts={'range_mask8','range_body_scale','range_M'}
    def run(p,cut):
        e={n:ring.atom(n)for n in p['free']}
        for n,op,a,b in p['source']:
            val=lambda v:ring.constant(v)if type(v)is int else e[v]
            e[n]=ring.atom('cut:'+n)if cut and n in cuts else ring.operation(op,val(a),val(b))
        return e
    old,new=run(parent,True),run(child,True)
    common=set(old)&set(new)-set(parent['free'])
    assert all(old[k]==new[k]for k in common)
    old,new=run(parent,False),run(child,False)
    for i,(a,b)in enumerate(child['comparisons']):
        if i!=4:assert ring.operation('-',old[a],old[b])==ring.operation('-',new[a],new[b])
    if child['range_lanes']==32:
        for f in FACTORS:
            if f!='index_unit':assert old[f]==new[f]
    return len(common)

def degree(p):
    main_norm_identity(p['source']);upper={n:1 for n in p['free']};curve={n:[0,1]for n in p['free']}
    for n,op,a,b in p['source']:
        da=upper[a]if type(a)is str else 0;db=upper[b]if type(b)is str else 0
        if n=='selection__R15':
            X,A,C,G,H=[upper[k]for k in ('selection__wn2','selection__R12','selection__R10a','selection__gam','selection__a4m5')]
            upper[n]=max(2*X,X+A+C,X+G,A+C+G,2*G,H+2*C)
        else:upper[n]=da+db if op=='*'else max(da,db)
        av=curve[a]if type(a)is str else[a%PRIME];bv=curve[b]if type(b)is str else[b%PRIME]
        curve[n]=dense_op(op,av,bv);assert len(curve[n])-1<=upper[n]
    expected=73+2*(29*p['a_scale']+7*32+106)
    assert upper[p['output']]==len(curve[p['output']])-1==expected
    fd=[upper[n]for n in FACTORS];assert fd==[len(curve[n])-1 for n in FACTORS]
    assert sum(fd)+6==expected
    return dict(exact_degree=expected,factor_degrees=fd,prime=PRIME,substitution='every free coordinate=t',nonzero_leading_coefficient=curve[p['output']][-1],full_coefficients_sha256=sha(stable(curve[p['output']])))

def partial(p,values):
    defs={r[0]:r[1:]for r in p['source']};cache=dict(values)
    def ev(v):
        if type(v)is int:return v
        if v not in cache:
            op,a,b=defs[v];x,y=ev(a),ev(b);cache[v]=x*y if op=='*'else x+y if op=='+'else x-y
        return cache[v]
    return ev

def path(edges,word):
    states={0:[]}
    for label in word:
        nxt={}
        for state,trace in states.items():
            for i,(a,b,l)in enumerate(edges):
                if l==label and a==state:nxt.setdefault(b,trace+[i])
        states=nxt
    assert 0 in states;return states[0]

def genuine_outer(p,x):
    u=24*x+13;assert x in (2,7)and u%5==1
    word=[2,3,6,7]+[1,5]*(u-1)
    trace=path(p['edges'],word);hist=[[1,u,1,u]]
    for label in word:
        row=hist[-1][:];i=(label-1)//2;row[i]+=(1 if label%2 else -1)*row[i^1];hist.append(row)
    assert hist[-1]==[0,1,0,1]
    # Independent fixture heights: double the author's minimum dyadic choices.
    bound=max(u,1+max(abs(v)for row in hist for v in row));D=2*(1<<bound.bit_length())
    B=16*D;pv=B**len(word);J=(pv-1)//(B-1)
    vals={'x':x,'height_slack':D-u}
    for k in range(4):vals['H'+str(k)]=sum((row[k]+D-1)*B**i for i,row in enumerate(hist[:-1]))
    for k in range(8):vals['Zhat'+str(k)]=1+sum((hist[i][(k//2)^1]+D-1)*B**i for i,l in enumerate(word)if l==k+1)
    for k in range(28):vals['controller__edge_hat'+str(k+1)]=1+sum(B**i for i,j in enumerate(trace)if j==k)
    vals['selection__bound_global']=pv+1-sum(vals['H'+str(k)]for k in range(4))-sum(vals['Zhat'+str(k)]for k in range(8))
    assert min(vals.values())>0
    ev=partial(p,vals);assert ev(P)==pv and ev(p['cuts']['computed_J'])==J
    assert ev('joint_bound_unit')==1
    for i,(a,b)in enumerate(p['comparisons']):
        if i!=4:assert ev(a)==ev(b)
    H,M,Z,q=[ev(k)for k in ('range_H','range_M','range_Z','selection__q')]
    assert H&M==Z and q==32*B*pv**p['a_scale']
    fs=[q-16*H-16*M+16*Z-15,16*(H-Z)+4,16*(M-Z)+2,16*Z+8]
    assert min(fs)>0 and sum(fs)==q-1 and [f%16 for f in fs]==[1,4,2,8]
    assert H<q//16 and M<q//16 and Z<q//16
    return dict(x=x,u=u,duration=len(word),D=D,B=B,word_sha256=sha(stable(word)),edge_path_sha256=sha(stable(trace)),endpoint=hist[-1],outer_residuals_zero=5,joint_unit=1,full_joined_AND=True,all_native_fields_positive=True,native_Pell_extension='theorem only; not materialized')

def pretyping_and_range(p):
    pre=0;typed=0
    for D in (40,43,64):
        B=16*D
        for J in (1,2,7):
            pv=(B-1)*J+1
            for sign in (-1,1):
                vals={'x':1,'height_slack':D-37,'selection__bound_global':pv+sign-12}
                vals.update({'H'+str(i):1 for i in range(4)});vals.update({'Zhat'+str(i):1 for i in range(8)})
                vals.update({'controller__edge_hat'+str(i+1):1+(J if i==pre%28 else 0)for i in range(28)})
                ev=partial(p,vals);assert min(vals.values())>0 and ev('joint_bound_unit')==sign and ev(P)==pv
                T2=pv**p['a_scale'];H,M,Z,q=[ev(k)for k in ('range_H','range_M','range_Z','selection__q')]
                assert 0<=ev('range_Hbody')<T2 and 0<=ev('range_Mbody')<T2 and 0<=Z<T2
                fs=[q-16*H-16*M+16*Z-15,16*(H-Z)+4,16*(M-Z)+2,16*Z+8]
                assert min(fs)>0 and sum(fs)==q-1 and [f%16 for f in fs]==[1,4,2,8]
                r=sum(f*q**i for i,f in enumerate(fs));X=q*(1+(q-1)*fs[3]);Y=3*q
                assert X*Y>2*r+3 and Y*(X+1)>2*r+3
                pre+=1
    for D in (1,2,4):
        B=16*D
        for t in (1,2):
            pv=B**t;J=(pv-1)//(B-1);rep=lambda n:sum(pv**i for i in range(n))
            short=(2*D-1)*J*rep(8);long=(2*D-1)*J*rep(32)
            assert long%pv**8==short
            for H in (0,short,short+1,pv**8-1,pv**7+pv+1):
                assert H<pv**8 and H&long==H&short;typed+=1
    return dict(pretyping_both_joint_sign_cases=pre,typed_range_equivalences=typed)

def verify(root,author_root):
    blobs,rec=authenticate(root,author_root);parent=json.loads(blobs['group_projective_inverse_macro_sharing.json'])['packets']['nielsen']
    counts=Counter();results={}
    assert parent['ledger']['operations']==371 and parent['ledger']['exact_degree']==4909
    defs={r[0]:r for r in parent['source']}
    assert defs['range_Bminus_shift']==['range_Bminus_shift','*','range_body_scale',2]
    assert [r[0]for r in parent['source']if 'range_Bminus_shift'in r[2:]]==['range_M']
    assert defs['range_M']==['range_M','+','range_Mbody','range_Bminus_shift']
    assert defs['range_mask8']==['range_mask8','*','range_cell','controller__origin_mask']
    assert defs['range_body_scale']==['range_body_scale','*','joint_scale','controller__flow_185']
    for variant,p in rec['packets'].items():
        separate=variant=='separate8';assert variant in ('separate8','reused32')
        own=[]
        for n,op,a,b in parent['source']:
            if n=='range_Bminus_shift':continue
            if separate and n=='range_mask8':
                own.append(['range_origin8','*',parent['cuts']['computed_J'],'controller__lane_repunit2']);b='range_origin8'
            if separate and n=='range_body_scale':b='controller__lane_power3'
            if n=='range_M':b='range_body_scale'
            own.append([n,op,a,b])
        assert same(own,p['source'])
        for field in ('free','auxiliaries','domains','comparisons','edges','positions','cuts','packing','flow'):assert same(parent[field],p[field]),field
        assert p['comparisons'][4]==['eight_units',1]and p['parameters']==['x']and p['output']=='joint_outer_output'
        assert p['m']==32 and p['a_scale']==(48 if separate else 72)and p['range_lanes']==(8 if separate else 32)and p['top_mask']==1
        assert not any(op=='*'and {a,b}=={parent['cuts']['computed_J'],'controller__lane_repunit2'}for n,op,a,b in parent['source'])
        ld=literal_ledger(p);expected=(371,150,221,54)if separate else(370,149,221,54)
        assert (ld['operations'],ld['M'],ld['A'],ld['witnesses'])==expected
        for field in ('operations','M','A'):assert ld[field]==p['ledger'][field]
        assert p['ledger']['certificate_operations']==ld['operations']-17 and p['ledger']['finalizer_operations']==17 and p['ledger']['comparisons']==6 and p['ledger']['positive_witnesses']==54
        finals={r[0]:r for r in parent['source']if r[0].startswith('joint_outer_')};current={r[0]:r for r in p['source']};assert len(finals)==17 and all(current[n]==r for n,r in finals.items())
        g=graph_cuts(p);s=joined_cuts(p);interfaces=interface_proof(parent,p);terms=finalizer_identity(p);deg=degree(p)
        assert p['degree_certificate']['exact_degree']==deg['exact_degree']
        assert [p['degree_certificate']['factor_degrees'][f]for f in FACTORS]==deg['factor_degrees']
        fixtures=[genuine_outer(p,x)for x in (2,7)];bounds=pretyping_and_range(p)
        for serial in range(6):
            vals={n:((i+2)*(serial+1)%5)-2 for i,n in enumerate(p['free'])}
            if serial>=4:vals={n:Fraction(v,3)for n,v in vals.items()}
            env=evaluate(p,vals)
            restored=dict(vals)
            for n,op,a,b in parent['source']:
                av=restored[a]if type(a)is str else a;bv=restored[b]if type(b)is str else b
                restored[n]=env[n]if n in ('range_mask8','range_body_scale','range_M')else(av*bv if op=='*'else av+bv if op=='+'else av-bv)
            assert all(restored[n]==env[n]for n in restored if n in env)
            counts['numeric_complete_changed_interfaces']+=1
            product=1
            for f in FACTORS:product*=env[f]
            sos=1+sum((env[a]-env[b])**2 for i,(a,b)in enumerate(p['comparisons'])if i!=4)
            assert env[p['output']]==product*sos-1
            counts['numeric_complete_finalizers']+=1
            if serial>=4:counts['rational_finalizers']+=1
        results[variant]=dict(ledger=ld,exact_degree=deg,graph_cuts=g,joined_cuts=s,changed_interface_registers=interfaces,full_finalizer_terms=terms,accepting_outer_fixtures=fixtures,bounds=bounds,source_sha256=sha(stable(p['source'])))
        counts['complete_sources']+=1;counts['paid_live_gates']+=ld['operations'];counts['graph_scale_polynomials']+=g['polynomials'];counts['joined_scalar_polynomials']+=s['polynomials'];counts['changed_interface_registers']+=interfaces;counts['unchanged_outer_residuals']+=5;counts['retained_finalizer_gates']+=17;counts['full_finalizer_expansions']+=1;counts['full_dense_degree_expansions']+=1;counts['genuine_accepting_outer_fixtures']+=2;counts.update(bounds)
    assert set(results)=={'separate8','reused32'}
    return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),author_pins=AUTHOR,dependency_pins=PINS,counts=dict(counts),results=results,scope=dict(historical_or_author_Python_executed=False,full_native_Pell_zeros_materialized=False,numerical_universal_bound=False,positive_outer_projection='general proof in companion note; fresh native extension',same_tuple_polynomial_identity=False,positive_tuple_bijection=False,entire_old_60_schedule_census_repeated=False))

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--author-root',type=Path);ap.add_argument('--expect',type=Path);ap.add_argument('--output',type=Path)
    a=ap.parse_args();r=verify(a.root.resolve(),(a.author_root or a.root).resolve());data=json.dumps(r,sort_keys=True,indent=2)+'\n';assert same(r,json.loads(data))
    if a.expect:assert same(r,json.loads(a.expect.read_text())),'Exact receipt mismatch'
    if a.output:a.output.write_text(data)
    print(json.dumps(dict(status='PASS',counts=r['counts']),sort_keys=True))
if __name__=='__main__':main()

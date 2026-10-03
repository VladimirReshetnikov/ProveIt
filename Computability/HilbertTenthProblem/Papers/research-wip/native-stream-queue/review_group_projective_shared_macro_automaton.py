#!/usr/bin/env python3
"""Independent bounded audit of the saved projective macro transfer."""
import argparse, hashlib, json
from collections import Counter, deque
from pathlib import Path


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


def local_cuts(packet):
    rows={r[0]:r[1:]for r in packet['source']}
    P='controller__geometry_power';cache={P:poly('P'),'B':poly('B')}
    def ev(v):
        if type(v)is int:return poly(v)
        if v in cache:return cache[v]
        if v not in rows:cache[v]=poly(v)
        else:
            op,a,b=rows[v];cache[v]=pop(op,ev(a),ev(b))
        return cache[v]
    edges=packet['edges'];positions=packet['positions'];n=len(edges)
    assert n in(7,8) and len(set(positions))==n and all(0<=p<8 for p in positions)
    hats=[f'controller__edge_hat{i+1}'for i in range(n)]
    fields=[add(poly(h),poly(1),-1)for h in hats]
    expected={'computed_J':{},'physical_Sbatch':{},'controller__edge_word':{},
              'controller__flow_left':{},'controller__flow_right':{}}
    expected.update({'history__dS'+str(i):{}for i in range(4)})
    for field,(a,b,label),pos in zip(fields,edges,positions):
        assert 1<=label<=8 and 0<=a<8 and 0<=b<8
        expected['computed_J']=add(expected['computed_J'],field)
        expected['physical_Sbatch']=add(expected['physical_Sbatch'],mul(field,ppow(poly('P'),label-1)))
        expected['controller__edge_word']=add(expected['controller__edge_word'],mul(field,ppow(poly('P'),pos)))
        expected['controller__flow_left']=add(expected['controller__flow_left'],mul(poly(a),field))
        expected['controller__flow_right']=add(expected['controller__flow_right'],mul(poly(b),mul(poly('B'),field)))
        k='history__dS'+str((label-1)//2)
        expected[k]=add(expected[k],field,1 if label%2 else -1)
    assert set(packet['cuts'])==set(expected)
    for name,e in expected.items():assert ev(packet['cuts'][name])==e,name
    return expected


def complete_reference(packet, template):
    """Compare against original saved source at independently proved scalar cuts."""
    cuts=local_cuts(packet);ring=RingDAG();free=set(packet['free'])
    abstract={k:(ring.constant(0)if not p else ring.atom('CUT:'+k))for k,p in cuts.items()}
    override={}
    for k,v in packet['cuts'].items():
        if type(v)is int:assert ring.constant(v)==abstract[k]
        elif v in override:assert override[v]==abstract[k]
        else:override[v]=abstract[k]
    child={r[0]:r[1:]for r in packet['source']}
    reference={r[0]:r[1:]for r in template['source']+template['polynomial_finalizer']}
    # These are the two inherited, separately proved native-interface changes.
    reference['range_Bminus_shift']=['*','range_body_scale',2]
    reference['selection__q']=['*',32,'range_Bshift']
    reference['shifted_native_quotient']=['+','selection__w','packed_z_product']
    reference['selection__Mbatch']=['*','controller__cell_minus1','REF:physical_Sbatch']
    ref_override=dict(abstract);ref_override['REF:physical_Sbatch']=abstract['physical_Sbatch']
    def engine(rows,over):
        cache=dict(over)
        def ev(v):
            if type(v)is int:return ring.constant(v)
            if v in cache:return cache[v]
            if v not in rows:
                assert v in free,v
                cache[v]=ring.atom(v)
            else:
                op,a,b=rows[v];cache[v]=ring.operation(op,ev(a),ev(b))
            return cache[v]
        return ev
    new,old=engine(child,override),engine(reference,ref_override)
    common=[v for v in child if v in reference and not v.startswith(('controller__flow','selection__Spack'))]
    for v in common:assert new(v)==old(v),v
    assert len(packet['comparisons'])==len(template['comparisons'])==6
    for (a,b),(c,d)in zip(packet['comparisons'],template['comparisons']):
        assert ring.operation('-',new(a),new(b))==ring.operation('-',old(c),old(d))
    assert new('joint_outer_output')==old('joint_outer_output')
    product=ring.constant(1)
    for name in FACTORS:product=ring.operation('*',product,new(name))
    assert new('eight_units')==product
    squares=ring.constant(1)
    for i,(a,b)in enumerate(packet['comparisons']):
        if i==4:continue
        res=ring.operation('-',new(a),new(b))
        squares=ring.operation('+',squares,ring.operation('*',res,res))
    assert new('joint_outer_output')==ring.operation('-',ring.operation('*',product,squares),ring.constant(1))
    finaldefs={r[0]:r for r in packet['source']}
    for name,op,a,b in template['polynomial_finalizer']:
        assert finaldefs[name]==[name,op,packet['cuts'].get(a,a),packet['cuts'].get(b,b)]
    return {'cuts':len(cuts),'common_registers':len(common),'comparisons':6,'whole_outputs':1,'ring_nodes':len(ring.nodes)}


def nfa_equivalence(left,right):
    def step(edges,states,label):return frozenset(b for a,b,l in edges if l==label and a in states)
    start=(frozenset([0]),frozenset([0]));seen={start};todo=deque([start])
    while todo:
        a,b=todo.popleft();assert (0 in a)==(0 in b)
        for l in range(1,9):
            state=(step(left,a,l),step(right,b,l))
            if state not in seen:seen.add(state);todo.append(state)
    return len(seen)

FACTORS=['first_unit','selection__R15','selection__P17','index_unit','linear_unit','strong_unit','joint_bound_unit']
PRIME=1000000007

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


def degree_proof(packet):
    rows=packet['source'];defs={r[0]:r[1:]for r in rows}
    guarded={
        'selection__R15':['-','selection__L15','selection__Ac2'],
        'selection__L15':['*','selection__R14','selection__R14'],
        'selection__R14':['+','selection__D1','selection__gam'],
        'selection__D1':['+','selection__wn2','selection__cam2'],
        'selection__cam2':['*','selection__R10a','selection__R12'],
        'selection__A':['+','selection__a_square','selection__a4m5'],
        'selection__a_square':['*','selection__R12','selection__R12'],
        'selection__Ac2':['*','selection__A','selection__c2'],
        'selection__c2':['*','selection__R10a','selection__R10a']}
    assert all(defs[k]==v for k,v in guarded.items())
    # Exact sparse coefficient proof in four independent atoms, before bounds.
    x,a,c,g,h=map(poly,('X','a','c','g','H'))
    root=add(add(x,mul(a,c)),g)
    original=add(mul(root,root),mul(add(mul(a,a),h),mul(c,c)),-1)
    expanded=add(add(add(add(mul(x,x),mul(poly(2),mul(x,mul(a,c)))),mul(poly(2),mul(x,g))),mul(poly(2),mul(a,mul(c,g)))),mul(g,g))
    expanded=add(expanded,mul(h,mul(c,c)),-1)
    assert original==expanded
    degree={v:1 for v in packet['free']};dense={v:[0,1]for v in packet['free']}
    for name,op,left,right in rows:
        dl=degree[left]if type(left)is str else 0;dr=degree[right]if type(right)is str else 0
        if name=='selection__R15':
            X,A,C,G,H=[degree[k]for k in('selection__wn2','selection__R12','selection__R10a','selection__gam','selection__a4m5')]
            degree[name]=max(2*X,X+A+C,X+G,A+C+G,2*G,H+2*C)
        else:degree[name]=dl+dr if op=='*'else max(dl,dr)
        a=dense[left]if type(left)is str else[left%PRIME]
        b=dense[right]if type(right)is str else[right%PRIME]
        dense[name]=dense_op(op,a,b)
        assert len(dense[name])-1<=degree[name]
    out='joint_outer_output'
    assert degree[out]==len(dense[out])-1==1789 and dense[out][-1]!=0
    factor_degrees=[degree[v]for v in FACTORS]
    assert factor_degrees==[247,442,308,196,196,392,2]
    assert [len(dense[v])-1 for v in FACTORS]==factor_degrees
    return {'exact_degree':1789,'factor_degrees':factor_degrees,'guarded_upper':degree[out],
            'prime':PRIME,'all_free_coordinates_substitution':'t',
            'full_dense_coefficient_digest':sha(stable(dense[out])),
            'nonzero_degree1789_coefficient':dense[out][-1]}


def partial_executor(packet,assignment):
    rows={r[0]:r[1:]for r in packet['source']};cache=dict(assignment)
    def value(v):
        if type(v)is int:return v
        if v not in cache:
            op,a,b=rows[v];x,y=value(a),value(b)
            cache[v]=x*y if op=='*'else x+y if op=='+'else x-y
        return cache[v]
    return value


def native_field_check(packet,assignment):
    ev=partial_executor(packet,assignment)
    H,M,Z=[ev(n)for n in('range_H','range_M','range_Z')]
    q=ev('selection__q');Q=q//16
    fields=[16*(Q-H-M+Z)-15,16*(H-Z)+4,16*(M-Z)+2,16*Z+8]
    assert all(v>0 for v in fields)and sum(fields)==q-1
    assert [v%16 for v in fields]==[1,4,2,8]
    r=sum(v*q**i for i,v in enumerate(fields))
    assert ev('selection__bs_packed')==r and r%16==1
    assert q**3+q**2+q+1<=r<q**4 and r<q**3*(fields[3]+1)
    assignment=dict(assignment,selection__w=1,selection__odd_half=1)
    val=partial_executor(packet,assignment)
    X,Y=val('selection__wn2'),val('selection__sn2')
    assert X==q*(1+(q-1)*fields[3])and Y==3*q
    assert X*Y>2*r+3 and val('selection__R12')>2*r+3
    return ev,(H,M,Z,q)


def graph_path(edges,word):
    candidates={0:[]}
    for label in word:
        following={}
        for state,path in candidates.items():
            for i,(a,b,l)in enumerate(edges):
                if a==state and l==label:following.setdefault(b,path+[i])
        candidates=following
    assert 0 in candidates
    return candidates[0]


def outer_checks(packet):
    codes=((1,1,2),(2,3,2),(4,5))
    choices=((0,),(1,),(2,),(0,1),(2,1),(1,0,2),(2,0,1,2))
    results=[]
    for serial,choice in enumerate(choices):
        word=sum((codes[i]for i in choice),())
        path=graph_path(packet['edges'],word)
        x=1+serial%3;u=24*x+13;history=[[1,u,1,u]]
        for label in word:
            state=list(history[-1]);k=(label-1)//2
            state[k]+=(1 if label%2 else-1)*state[k^1]
            history.append(state)
        assert history[-1][3]==u and u>1
        magnitude=max(abs(v)for row in history for v in row)
        D=1<<(max(magnitude+1,u)).bit_length()
        B=16*D;P=B**len(word);J=(P-1)//(B-1)
        assign={'x':x,'height_slack':D-u}
        for k in range(4):assign['H'+str(k)]=sum((row[k]+D-1)*B**i for i,row in enumerate(history[:-1]))
        for k in range(8):assign['Zhat'+str(k)]=1+sum((history[i][(k//2)^1]+D-1)*B**i for i,l in enumerate(word)if l==k+1)
        for i in range(len(packet['edges'])):assign[f'controller__edge_hat{i+1}']=1+sum(B**j for j,e in enumerate(path)if e==i)
        assign['selection__bound_global']=P+1-sum(assign['H'+str(k)]for k in range(4))-sum(assign['Zhat'+str(k)]for k in range(8))
        assert min(assign.values())>0
        ev,scalar=native_field_check(packet,assign)
        assert ev('controller__geometry_power')==P and ev(packet['cuts']['computed_J'])==J
        assert ev(packet['cuts']['controller__flow_left'])==ev(packet['cuts']['controller__flow_right'])
        H,M,Z,q=scalar;assert H&M==Z and q==32*B*P**24
        assert ev('joint_bound_unit')==1
        for k in range(4):assert ev('history__left'+str(k))-ev('history__right'+str(k))==P*(history[-1][k]-(k%2))
        assert ev('history__left3')-ev('history__right3')==P*(u-1)>0
        results.append({'duration':len(word),'x':x,'target_satisfied':False,'last_coordinate':u})
    # Before typing: arbitrary nonnegative edge fields, nondyadic B/P included,
    # and both possible joint-unit signs. These are deliberately not full zeros.
    nontyped=0
    for D in(40,41,64):
        B=16*D
        for J in(1,2,5):
            P=(B-1)*J+1
            for sign in(-1,1):
                assign={'x':1,'height_slack':D-37,'selection__bound_global':P+sign-12}
                assign.update({'H'+str(i):1 for i in range(4)})
                assign.update({'Zhat'+str(i):1 for i in range(8)})
                assign.update({f'controller__edge_hat{i+1}':1+(J if i==0 else 0)for i in range(len(packet['edges']))})
                assert min(assign.values())>0
                ev,scalar=native_field_check(packet,assign)
                assert ev('joint_bound_unit')==sign and ev('controller__geometry_power')==P
                nontyped+=1
    return {'genuine_path_and_AND_fixtures':results,'pretyping_both_sign_cases':nontyped}


DEPENDENCIES = {'../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md': '47a2c5b69f3c87b7a1ddc61ef84757023de291b63d1330e2c8dc9b40e811ab8b',
 '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b',
 '../../1980/PELL_RELAXED_AUXILIARY_PROOF.md': '9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90',
 'group_macro_automaton_sharing.json': '8e7044b66bebbacc0f89721807369607146b57bb67b14d1ddb9c4e05586a681b',
 'group_macro_automaton_sharing.md': 'e253a396f999e8045bb1c4ee223602907f8ea003b7b7f3d93218cb425ffd5585',
 'group_macro_automaton_sharing.py': 'f9d660c3309c030c98c8209f2b8a708a6731eedf62234d459ed4fa3f1db2af48',
 'group_projective_coupled_linear_unit.md': '15fa0737a82996a8ea5c28aa62cbbe798ac5e06e4a3323c4dcaa01c9cd6286c7',
 'group_projective_idle_free_paths.md': '0cc8b21be7fca0cc5763ba3862f6888f94669259ca26beb0050cd5f8ef1ec9e9',
 'group_projective_joint_bound_unit.md': '3f33f4d7c04137409688b011859578924a4d1571d46d37bf1ca7ebd81a230a1e',
 'group_projective_joint_first_norm.md': 'da7f6baaedaecae3166cfed050d2e913d26b280cc3332ca04bf0e8983417e9cb',
 'group_projective_label_aligned_lanes.json': '232fbc5d9409da72f7f8b0335316920c93cb435bbcbb43ce122b3b8c17477008',
 'group_projective_label_aligned_lanes.md': '66221327c058b335febda310bb81b656b7c7095fb4463d633f60de9cd8213edb',
 'group_projective_label_aligned_lanes.py': 'cbecb51a164f7e4272a293fc2cb6e549838ec153b693399487e3ee0b4dd8c9a5',
 'group_projective_output_bound_obstruction.md': 'b478f73d003a62ed530ba329c01f875be7a5da2202b746d89ccd50f8f50aa56b',
 'group_projective_padded_program_margin.md': 'a4ad4487f682d250f3a9ae84cc8f4182b21d2e216fa0d53624f7368abd028952',
 'group_projective_port_bias_folding.md': 'e699bb645378ced31c62dd9bb702eb6ed0ea93be8b6ee91e1cdc859b27e3c706',
 'group_projective_product_radix_scale.json': '1403987d49c3613b3ca6cdc1f1794d16199af9020c9c88fd53c49981f95db9a7',
 'group_projective_product_radix_scale.md': 'f342dbc1da849a7c74cc7043becad6d218582adeefffa55dec558a28b1e47b39',
 'group_projective_product_radix_scale.py': 'd33e8aa3bff7559c72768be7116f0328ebad0cf65190115101457a71a0e25965',
 'group_projective_reindexed_edge_geometry.md': 'ceadd45bebece376f9cbaa5e7be1740f35510a55211819376fa335ad719152d3',
 'group_projective_shared_flow_target.md': '17bc108499565d3cbc5a6c55ca9395693c8fcce5c72069f5080560702424d1e4',
 'group_projective_shared_flow_target.py': 'eea982ef140ac046f9fe857747fdde82a51bedc78f22306558941ab839eeacf0',
 'group_projective_shared_selector_pack.md': 'b29225304b4a3b96c922df5645ca7060adc60c3074ed20e561a8e074dc411d66',
 'group_projective_shifted_X_quotient.md': '4f76dda46f9385a769da0c809292b466d352be2a6f2d39c5e70519bdeda37e00',
 'group_projective_strong_unit_product.md': '06978175efe47f59bf497f8882b3138692abead1458c58de6a53af92b4f83605',
 'group_projective_tail_quotient_shift.json': 'a422e7a65df26e626f3c36f97a53a68805b86806be3dc35d35e7d49a17b80b27',
 'group_projective_tail_quotient_shift.md': 'a1e1e67df618f6f809c2e85a409509b288337f62cd1af35cfc6ca950e0efa92a',
 'group_projective_tail_quotient_shift.py': '08248ad763113a6a2e60168edfd058b92be4e14b2f7932fa1be66eb406a70610',
 'group_projective_zero_mortality6.md': 'c0f3cb53d8a189dd7b98e0deb892a75e64426e8ac480ee049f945ed09e896bc2',
 'group_sparse_macro_flow.md': '4e4356902a52de1464c91ac5aea2a654900492b74ee252d9ea22a34e5dd6febc',
 'group_sparse_macro_flow.py': '74604c1a9d1071a823e0df3388d2c89eb639cf3e088a39fa7fff3eae5113238a',
 'native_controller_binary_selector56.md': '97fcdc7188f968f2ac3e315249b0e0a15dcc787c10451924ad3f2551c8bb376c'}
AUTHOR = {'group_projective_shared_macro_automaton.json': '284da792cce620169ebca9cae7ee77488b56fe0f68c47cf12059af5d0e980497',
 'group_projective_shared_macro_automaton.md': '5933851785599c3c83bbddc28f1dbe2e43c7db17ed256a87a5dd293117bc9eb6',
 'group_projective_shared_macro_automaton.py': '2cbbc82d18e0e175d3c7f44707fdc16c2bf899aaad5deafa44c0975cf0b96bf7'}

def exact(a,b):
    if type(a)is not type(b):return False
    if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
    if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
    return a==b


def authenticate(directory,pins):
    result={}
    for name,h in pins.items():
        data=(directory/name).read_bytes()
        if sha(data)!=h:raise ValueError('Dependency bytes differ: '+name)
        result[name]=data
    return result


def verify(root,author_root):
    blobs=authenticate(root,DEPENDENCIES);author_blobs=authenticate(author_root,AUTHOR)
    author=json.loads(author_blobs['group_projective_shared_macro_automaton.json'])
    assert author['source_sha256']==AUTHOR['group_projective_shared_macro_automaton.py']
    assert exact(author['pins'],DEPENDENCIES)
    assert author['fixture']==[[1,1,2],[2,3,2],[4,5]]
    template=json.loads(blobs['group_projective_label_aligned_lanes.json'])['source']['source_example']
    assert template['m']==8 and template['compute_length']is True and template['controller_mask']is True
    assert template['source'][:5]==[['history__input_product','*',24,'x'],['history__u','+', 'history__input_product',13],['D','+','history__u','height_slack'],['history__c0','-','D',1],['B','*',16,'D']]
    private=[];nextstate=1
    for word in ((1,1,2),(2,3,2),(4,5)):
        current=0
        for i,label in enumerate(word):
            target=0 if i==len(word)-1 else nextstate
            if target:nextstate+=1
            private.append([current,target,label]);current=target
    shared=[[0,2,1],[0,3,2],[0,4,4],[1,0,2],[2,1,1],[3,1,3],[4,0,5]]
    graphs={'private':private,'shared':shared}
    assert all(1<=e[2]<=5 for graph in graphs.values()for e in graph)
    subsets=nfa_equivalence(private,shared)
    assert subsets==author['language_subset_pairs']==7
    results={};totals=Counter()
    for graph,p in author['packets'].items():
        assert graph in graphs and p['edges']==graphs[graph]
        assert p['graph']==graph
        assert p['positions']==({'private':[0,1,2,3,5,4,6,7],'shared':[5,6,3,1,0,2,4]}[graph])
        assert p['packing']==({'private':'direct','shared':'grouped'}[graph])
        prefix=p['source'][:5]
        assert prefix==template['source'][:5]
        assert p['free']==['x']+[v for v in template['auxiliaries']if not v.startswith('controller__edge_hat')]+[f'controller__edge_hat{i+1}'for i in range(len(p['edges']))]
        ledger=literal_ledger(p)
        assert (ledger['operations'],ledger['M'],ledger['A'],ledger['witnesses'])==({'private':(236,99,137,34),'shared':(230,98,132,33)}[graph])
        assert p['ledger']==({k:ledger[k]for k in('operations','M','A')}|{'degree_upper':1789,'exact_degree':1789,'naive_degree_upper':1839,'certificate_operations':ledger['operations']-17,'finalizer_operations':17,'positive_witnesses':ledger['witnesses'],'comparisons':6})
        proof=complete_reference(p,template);degree=degree_proof(p);outer=outer_checks(p)
        assert p['degree_certificate']['exact_degree']==degree['exact_degree']
        assert p['degree_certificate']['factor_degrees']==dict(zip(FACTORS,degree['factor_degrees']))
        results[graph]={'source_sha256':sha(json.dumps(p['source'],separators=(',',':')).encode()),
                        'ledger':ledger,'certificate_ledger':{'M':ledger['M']-6,'A':ledger['A']-11,'operations':ledger['operations']-17},
                        'whole_interface':proof,'degree':degree,'outer':outer}
        totals.update(paid_live_gates=len(p['source']),sources=1,coefficient_cut_identities=proof['cuts'],
                      static_register_identities=proof['common_registers'],comparisons=6,whole_outputs=1,
                      finalizer_gates=17,complete_dense_degree_proofs=1,
                      genuine_path_AND_interfaces=len(outer['genuine_path_and_AND_fixtures']),
                      pretyping_both_sign_interfaces=outer['pretyping_both_sign_cases'])
    assert set(results)==set(graphs)
    # The other28 schedules are authenticated metadata only. Check coverage,
    # summary consistency, and winner selection; do not pretend their arrays
    # were independently reconstructed by this two-source review.
    records=author['records'];assert len(records)==30
    coverage={}
    for graph in graphs:
        subset=[r for r in records if r['graph']==graph]
        maps={tuple(r['positions'])for r in subset}
        assert len(maps)==5 and len(subset)==15
        for pos in maps:
            assert len(pos)==len(graphs[graph])and len(set(pos))==len(pos)and all(0<=i<8 for i in pos)
            assert sorted(r['packing']for r in subset if tuple(r['positions'])==pos)==['direct','grouped','shared']
        best=min(subset,key=lambda r:(r['ledger']['operations'],r['ledger']['M'],r['packing'],r['positions']))
        assert best['source_sha256']==results[graph]['source_sha256']
        coverage[graph]={'metadata_schedules':15,'injections':5,'winner_hash':best['source_sha256']}
    assert sum(r['ledger']['operations']for r in records)==author['counts']['paid_live_gates']==7239
    # Independent elementary sign exclusions used before the native rank theorem.
    exclusions=0
    for a in range(4):
        D=(a*a+4*a+3)%4
        for c in range(4):
            for t in range(4):
                assert (t*t-D*c*c)%4!=3
                assert (1+t*t-D*(c*c-1))%4!=3
                exclusions+=2
    for t in range(4):
        for v in range(4):
            for y in range(4):
                assert (t*t*(v*v-y*y)+y*y)%4!=3
                exclusions+=1
    assert all((g*g)%4!=3 for g in range(4));exclusions+=4
    totals['unit_mod4_cases']=exclusions
    assert totals['paid_live_gates']==466 and totals['static_register_identities']==366
    return {'status':'PASS','schema':'review-group-projective-shared-macro-v1',
            'source_sha256':sha(Path(__file__).read_bytes()),'author_pins':dict(AUTHOR),
            'dependency_pins':dict(DEPENDENCIES),'counts':dict(totals),
            'exact_language_subset_pairs':subsets,'winners':results,
            'authenticated_schedule_metadata':coverage,
            'scope':{'actual_sources_independently_checked':2,'other_schedule_arrays_rebuilt':False,
                     'other_schedule_coverage_and_minima':'authenticated metadata consistency only',
                     'empty_fixture_input_relation':True,
                     'empty_relation_reason':'letters7/8 are absent; coordinate3 remains24*x+13>1',
                     'complete_native_Pell_zeros_materialized':False,
                     'across_graph_polynomial_identity':False,'across_graph_positive_bijection':False,
                     'numerical_universal_bound':False,'global_packing_optimum':False,
                     'author_or_historical_Python_executed':False,
                     'maintained_public_API_review':False}}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root',type=Path,required=True)
    ap.add_argument('--author-root',type=Path)
    ap.add_argument('--output',type=Path)
    ap.add_argument('--expect',type=Path)
    args=ap.parse_args();root=args.root.resolve();author_root=(args.author_root or root).resolve()
    result=verify(root,author_root)
    encoded=json.dumps(result,sort_keys=True,indent=2)+'\n'
    assert exact(result,json.loads(encoded))
    if args.expect:assert exact(result,json.loads(args.expect.read_text())),'Receipt mismatch'
    if args.output:args.output.write_text(encoded)
    print(json.dumps({'status':'PASS','counts':result['counts']},sort_keys=True))

if __name__=='__main__':main()

#!/usr/bin/env python3
"""Finite complete first-root grouping families; authenticated JSON sources only.

No historical Python modules are executed. See the companion note for the
positive-zero coordinate proof and the exact, deliberately finite scope.
"""
import argparse
from collections import Counter
from copy import deepcopy
from fractions import Fraction
from functools import lru_cache
import hashlib
import json
from math import isqrt, prod
from pathlib import Path
import random
import tempfile
if not __debug__:
    raise RuntimeError('Run without -O')
PINS = {'complete75_asymmetric_scale_tradeoffs.py': 'a87578023ae99433519555a3d1f566c853a4b6a8323ab566a72fc9108acb6660', 'complete75_asymmetric_scale_tradeoffs.json': '47a059a8871c101466d7d0440cf39c5dda4ddffd55fcc8d8ac118874aedbac98', 'complete75_asymmetric_scale_tradeoffs.md': '3fb7aad219cc05570531c2e806bd4f4998681777963063761106400514a146c2', 'complete75_asymmetric_factor_partitions.py': 'b772fc579454b13ce30e5f9feaad25206d35b04af3cb4dffb1d76d1246d4c515', 'complete75_asymmetric_factor_partitions.json': '6d9112e67d18306bb6aa8aaf8660432d7dff2398e198c3018907e1c79c70a42f', 'complete75_asymmetric_factor_partitions.md': '1e54eb9a8b5e704947ed78d69716c79ec2e6e46d187e700960bf1b1b700eebf2', 'complete75_linear_input_modulus89.py': 'dfcee79fb8564a29bba3a243da4fbce848709d0de5117426222b39b869ef4efb', 'complete75_linear_input_modulus89.json': 'c6758bc90adeb331ddfb8e9512d8974035e46701cd0a2c4ebd378b5f7c59c9fd', 'complete75_linear_input_modulus89.md': '855a1e038dac816043c040decd35d33818e0da25e1e9e1713a9a454bcc531444', 'complete75_linear_input_degree_tradeoffs.py': 'cd06f404f5a9cbb0f5b6116ba13498321bfeba845f827541833ef4a1f3c882bc', 'complete75_linear_input_degree_tradeoffs.json': '15f62dee3287c5a3d976f43add43e74e755f8e7e2b59787b837c87c2cdf35d84', 'complete75_linear_input_degree_tradeoffs.md': '8b3cb44cbd2b979175ebfe4731556384469adfa93890ca7b01f70fa192a9682b', 'complete75_auxiliary_gap_degree_tradeoffs.py': 'f359f6d07c8c8e18d1f41b53e198f1bba70f5d43dcad049e1e12600260521312', 'complete75_auxiliary_gap_degree_tradeoffs.json': '741592f41a1ef6df2797a23e1380e3c208b093379b0379a4aedf36700f9592d9', 'complete75_auxiliary_gap_degree_tradeoffs.md': '315792b00530a4517e7f79f3c423f860268145803eb9bc364a235782aad69755', 'complete86_factored_first_root.py': '29cf4100b846bcbabb05185550b7d9ead6b572746048b94998a13c83eeaff40f', 'complete86_factored_first_root.json': '2dfe46fe9c5537ff51eb3c542806c58242238363e6018f9daab7eabf0b6fe61e', 'complete86_factored_first_root.md': '9f2b50449e0724e523e9dd5d022f229b77504976f23ee52ca2917cf11ceb322b', 'complete75_normalized_strong87.py': '7dae1b0038cb15ce197e03ff5c75a68f294b811cc200b6cafb3cbf5c24867cf8', 'complete75_coupled_index_linear88.py': 'e43dc5c65659ab8526817f674384b1faaf324671e8e24ccc82b72f3b4e8c7aed', 'complete75_positive_elimination.py': '70123af4f0787b38271f7c4f0fa60e4235cd2f1964ee1b0ad345fe0e3bb82749', 'complete75_asymmetric_linear_gap_tradeoffs.py': 'a08626905d8a790ec1458bc8e7302b9f28e251b84818695d2fa3c640a8c9dcf2', 'complete75_asymmetric_linear_gap_tradeoffs.json': 'dcd2c462e8405bc4535682a624832e8a8ad044a86504fd0b46df6700ab5c0f26', 'complete75_asymmetric_linear_gap_tradeoffs.md': '93aac323a64bf6c7e8946faeddf90de5606d8c133d3bd611a0806269e8f92638'}
CONSTANTS = ['Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF']
FACTORS = ['norm_first','norm_main','norm_input','norm_aux','norm_index',
           'norm_transport','norm_strong','norm_linear']
KINDS = ['asymmetric_normalized','asymmetric_ordinary','asymmetric_comparison'] + [
    prefix+'_'+family for prefix in ('linear','auxgap')
    for family in ('coupled_units','uncoupled_units','coupled_comparison',
                   'uncoupled_comparison','six_comparisons')]
OLD_BLOCK = {
 'tau_square':['*','tau_gap','tau_gap'],
 'first_root_base':['*','UM','ksn2'],
 'twice_tau_gap':['+','tau_gap','tau_gap'],
 'first_signed_gap':['-','twice_tau_gap','R10b'],
 'first_cross':['*','first_root_base','first_signed_gap'],
 'norm_first':['+','tau_square','first_cross']}

def need(ok, message):
    if not ok: raise ValueError(message)
def sha(raw): return hashlib.sha256(raw).hexdigest()
def canonical_bytes(value): return json.dumps(value,sort_keys=True,separators=(',',':')).encode()
def exact(a,b):
    if type(a) is not type(b): return False
    if type(a) is dict: return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if type(a) in (tuple,list): return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b

def _authenticate(root):
    root=Path(root)
    need(bool(PINS),'Pinned source inventory required')
    for name,pin in PINS.items():
        need(sha((root/name).read_bytes())==pin,'Pinned parent '+name)
    return root

def ancestors(rows, terminals):
    nodes={row[0]:row for row in rows}; live=set()
    def visit(value):
        if type(value) is str and value in nodes and value not in live:
            live.add(value)
            for v in nodes[value][2:]:visit(v)
    for value in terminals: visit(value)
    return [deepcopy(row) for row in rows if row[0] in live]

def inspect(rows,terminals,witnesses):
    need(type(rows) is list,'Exact source container')
    ready=set(CONSTANTS+witnesses+['x']);seen=set();counts=Counter()
    for row in rows:
        need(type(row) is list and len(row)==4,'Exact source row')
        n,op,a,b=row
        need(type(n) is str and n not in ready and type(op) is str and op in ('+','-','*'),'Fresh legal gate')
        need(all(type(v) is int or type(v) is str and v in ready for v in (a,b)),'Typed closed operands')
        ready.add(n);seen.add(n);counts[op]+=1
    need(len(ancestors(rows,terminals))==len(rows),'Every paid gate live')
    used={v for _,_,a,b in rows for v in (a,b) if type(v) is str and v not in seen}
    need(used==set(CONSTANTS+witnesses+['x']),'Complete fixed/witness/input interface')
    return dict(operations=len(rows),M=counts['*'],A=counts['+']+counts['-'],
                positive_witnesses=len(witnesses),all_gates_live=True)

def execute(rows,values):
    e=dict(values)
    for n,op,a,b in rows:
        a=a if type(a) is int else e[a];b=b if type(b) is int else e[b]
        e[n]=a*b if op=='*' else a+b if op=='+' else a-b
    return e

@lru_cache(None)
def _parents_cached(root_string):
    root=Path(root_string)
    load=lambda stem:json.loads((root/(stem+'.json')).read_text())
    asym=load('complete75_asymmetric_scale_tradeoffs')['source']
    lin=load('complete75_linear_input_modulus89')['source']
    lu=load('complete75_linear_input_degree_tradeoffs')['variants']['90_degree132']['source']
    gap=load('complete75_auxiliary_gap_degree_tradeoffs')['variants']
    direct={x['name']:x for x in load('complete75_asymmetric_linear_gap_tradeoffs')['direct_transfers']}
    data={}
    for kind in KINDS:
        outside=[]
        if kind.startswith('asymmetric'):
            normalized=kind=='asymmetric_normalized';source=asym[0 if normalized else 1]
            rows=source['source'];witnesses=source.get('positive_witnesses')
            if witnesses is None:
                witnesses=['Jrep','F','alpha','zplus','f','h','i','j','o','s','w','tau_gap',
                           'eta','zeta','y_aux','Z','delta','rho','sigma']
            factors=FACTORS[:];weights=[12,18,32,56 if normalized else 24,7,3,34 if normalized else 22,7]
            origin='complete75_asymmetric_scale_tradeoffs.json'
            if kind=='asymmetric_comparison':
                del factors[6];del weights[6];outside=[['ic22','R16']]
        else:
            prefix,family=kind.split('_',1);uncoupled=family.startswith('uncoupled') or family=='six_comparisons'
            if prefix=='linear':
                source=lu if uncoupled else lin
                origin='complete75_linear_input_degree_tradeoffs.json' if uncoupled else 'complete75_linear_input_modulus89.json'
            else:
                source=gap['91_degree128' if uncoupled else '90_degree131']['source']
                origin='complete75_auxiliary_gap_degree_tradeoffs.json'
            witnesses=source.get('positive_witnesses',source.get('retained_positive_witnesses'))
            directname=('linear_90_degree132' if uncoupled else 'linear89') if prefix=='linear' else ('gap_91_degree128' if uncoupled else 'gap_90_degree131')
            rows=direct[directname]['source'];origin='complete75_asymmetric_linear_gap_tradeoffs.json:'+directname
            factors=FACTORS[:];weights=[12,18,20,20 if prefix=='auxgap' else 24,7,3,22,6 if uncoupled else 7]
            if family.endswith('comparison') or family=='six_comparisons':
                del factors[6];del weights[6];outside=[['ic22','R16']]
            if family=='six_comparisons':
                factors.pop();weights.pop();outside.append(['H17','aux_u_rhs'])
        need(type(witnesses) is list and len(witnesses)==19,'Nineteen supplied parent witnesses')
        core=ancestors(rows,factors+[x for pair in outside for x in pair])
        d={n:[op,a,b] for n,op,a,b in core}
        for n,row in {'wn2':['*','w','q'],'sn2':['*','s','n2'],'n2':['*','Lbig','q'],
                      'UM':['*','wn2','sn2'],'ksn2':['*','R10b','sn2'],'R10b':['+','eta','zeta']}.items():
            need(exact(d.get(n),row),'Actual asymmetric scale and first-root producer: '+n)
        need(all(exact(d.get(n),row) for n,row in OLD_BLOCK.items()),'Literal six-gate parent norm')
        need({n for n,op,a,b in core if 'tau_gap' in (a,b)}=={'tau_square','twice_tau_gap'},'Private first coordinate')
        if outside:
            need(exact({n:[op,a,b] for n,op,a,b in rows}['norm_strong'],['+','strong_difference',1]),'Strong unit identity')
        if len(outside)==2:
            need(exact(d['H17'],['-','jc','r_lhs']),'Actual uncoupled linear comparison')
        ledger=inspect(core,factors+[x for pair in outside for x in pair],witnesses)
        data[kind]=dict(kind=kind,source=core,factors=factors,weights=weights,
            ordinary_comparisons=outside,residual_degrees=([22] if outside else [])+([6] if len(outside)==2 else []),
            witnesses=witnesses,fixed_numerals=CONSTANTS[:],ordinary_input='x',
            origin=origin,core_ledger=ledger,source_sha256=sha(canonical_bytes(core)),
            scope='Complete corresponding parent positive zero set; fixed admissible compiler numerals and ordinary positive input.')
    return data

def canonical_parent(root,kind='asymmetric_comparison'):
    need(type(kind) is str and kind in KINDS,'Exact selected family')
    root=_authenticate(root)
    return deepcopy(_parents_cached(str(root.resolve()))[kind])

def _rewrite_base(parent):
    rows=[]
    for n,op,a,b in parent['source']:
        if n=='tau_square':rows.append([n,'*','tau_root','tau_root'])
        elif n=='norm_first':
            rows += [['first_next','+','first_root_base','R10b'],
                     ['first_product','*','first_root_base','first_next'],
                     ['norm_first','-','tau_square','first_product']]
        elif n not in ('twice_tau_gap','first_signed_gap','first_cross'):
            rows.append([n,op,a,b])
    b=deepcopy(parent);b['source']=rows;b['weights'][0]=22
    b['witnesses']=['tau_root' if n=='tau_gap' else n for n in b['witnesses']]
    b['core_ledger']=inspect(rows,b['factors']+[x for pair in b['ordinary_comparisons'] for x in pair],b['witnesses'])
    need(b['core_ledger']['operations']==parent['core_ledger']['operations']-1,'One paid addition saved')
    need(b['core_ledger']['M']==parent['core_ledger']['M'],'Unchanged multiplication total')
    b['source_sha256']=sha(canonical_bytes(rows));b['parent_core_sha256']=parent['source_sha256']
    b['coordinate_map']={'forward':'tau_root=first_root_base+tau_gap','inverse':'tau_gap=tau_root-first_root_base',
        'scope':'Full positive-zero bijection; polynomial graph identity on all integer or rational tuples.',
        'positivity_before_parent':'Grouped zero implies norm_first=+1 or -1; T²-L²=L*k+norm_first>0 since L>0,k>=2.'}
    return b

def base(root,kind='asymmetric_comparison',supplied=None):
    parent=canonical_parent(root,kind)
    if supplied is not None:need(exact(supplied,parent),'Only the complete canonical selected parent')
    return _rewrite_base(parent)

def _plan(partition,anchor,n):
    need(type(partition) is list and partition and all(type(g) is list and g for g in partition),'Exact nonempty partition lists')
    need(all(type(i) is int for g in partition for i in g),'Exact integer factor indices')
    need(sorted(i for g in partition for i in g)==list(range(n)),'Every factor exactly once')
    need(all(g==sorted(g) for g in partition) and [g[0] for g in partition]==sorted(g[0] for g in partition),'Canonical ordered partition')
    need(anchor is None or type(anchor) is int and 0<=anchor<len(partition),'Exact valid anchor')

def _degree(b,p,anchor):
    ds=[sum(b['weights'][i] for i in g) for g in p];r=max([0]+b['residual_degrees'])
    degree=2*max([r]+ds) if anchor is None else ds[anchor]+2*max([r]+[d for i,d in enumerate(ds) if i!=anchor])
    return dict(exact_degree=degree,factor_degrees=b['weights'][:],group_degrees=ds,retained_residual_degrees=b['residual_degrees'][:])

def _emit(b,partition,anchor):
    _plan(partition,anchor,len(b['factors']));rows=deepcopy(b['source']);products=[]
    for j,g in enumerate(partition):
        last=b['factors'][g[0]]
        for k,i in enumerate(g[1:]):
            n=f'root_group_{j}_{k}';rows.append([n,'*',last,b['factors'][i]]);last=n
        products.append(last)
    certificate=deepcopy(rows);pairs=deepcopy(b['ordinary_comparisons'])+[[v,1] for i,v in enumerate(products) if i!=anchor]
    last=None
    for i,(a,bb) in enumerate(pairs):
        r=f'root_residual_{i}';s=f'root_square_{i}';rows.extend([[r,'-',a,bb],[s,'*',r,r]])
        if last is None:last=s
        else:n=f'root_sum_{i}';rows.append([n,'+',last,s]);last=n
    if anchor is not None:
        if last is None:rows.append(['polynomial','-',products[anchor],1])
        else:rows.extend([['root_positive','+',last,1],['root_anchored','*',products[anchor],'root_positive'],['polynomial','-','root_anchored',1]])
        output='polynomial'
    else:output=last
    ledger=inspect(rows,[output],b['witnesses']);c=inspect(certificate,products+[x for pair in b['ordinary_comparisons'] for x in pair],b['witnesses'])
    n=len(b['factors']);g=len(partition);m=len(b['ordinary_comparisons']);special=m==0 and g==1 and anchor==0
    need(ledger['operations']==b['core_ledger']['operations']+n+3*m+2*g-1-int(special),'Fully paid finalizer formula')
    return dict(base=b,partition=deepcopy(partition),anchor=anchor,group_products=products,
        certificate_source=certificate,certificate_ledger=c,equations=m+g,
        polynomial_source=rows,output=output,ledger=ledger,degree_certificate=_degree(b,partition,anchor),
        finalizer='SOS' if anchor is None else 'integer_unit_anchor',
        empty_residual_finalizer=special)

def build(root,kind='asymmetric_comparison',partition=None,anchor=None):
    b=base(root,kind)
    if partition is None:partition=[[0,1],[2,4],[3,5,6]] if kind=='asymmetric_comparison' else [list(range(len(b['factors'])))]
    return _emit(b,partition,anchor)

def checked(root,packet):
    need(type(packet) is dict and type(packet.get('base')) is dict,'Exact complete packet')
    b=packet['base'];need(type(b.get('kind')) is str,'Exact selected kind')
    expected=build(root,b['kind'],packet.get('partition'),packet.get('anchor'))
    need(exact(packet,expected),'Complete canonical typed packet required')
    return expected

def polynomial_source(root,packet):
    p=checked(root,packet);return p['polynomial_source'],p['output']

def evaluate(root,packet,values,*,signed=False):
    p=checked(root,packet);need(type(signed) is bool,'Exact Boolean domain switch')
    names=p['base']['witnesses']+CONSTANTS+['x']
    need(type(values) is dict and set(values)==set(names),'Exact complete supplied assignment')
    need(all(type(v) is int for v in values.values()),'Exact integer coordinates')
    need(signed or all(v>0 for v in values.values()),'Strictly positive supplied coordinates')
    return execute(p['polynomial_source'],values)[p['output']]

def coordinate(root,packet,values,*,to_parent=False,positive=False):
    p=checked(root,packet);need(type(to_parent) is bool and type(positive) is bool,'Exact graph mode flags')
    names=p['base']['witnesses']+CONSTANTS+['x']
    if not to_parent:names=['tau_gap' if n=='tau_root' else n for n in names]
    need(type(values) is dict and set(values)==set(names) and all(type(v) is int for v in values.values()),'Exact complete integer graph tuple')
    if positive:need(all(v>0 for v in values.values()),'Positive starting graph tuple')
    get=dict(values)
    if not to_parent:get['tau_root']=0
    L=execute(ancestors(p['base']['source'],['first_root_base']),get)['first_root_base']
    result=dict(values)
    if to_parent:result['tau_gap']=result.pop('tau_root')-L
    else:result['tau_root']=result.pop('tau_gap')+L
    if positive:need(all(v>0 for v in result.values()),'Inverse positivity is guaranteed on zeros only')
    return result

def partitions(n):
    groups=[]
    def visit(i):
        if i==n:yield deepcopy(groups);return
        for g in groups:
            g.append(i);yield from visit(i+1);g.pop()
        groups.append([i]);yield from visit(i+1);groups.pop()
    yield from visit(0)

def _objectives(b):
    best={};count=choices=0;h=hashlib.sha256();n=len(b['factors']);m=len(b['ordinary_comparisons'])
    for p in partitions(n):
        count+=1;g=len(p)
        for a in [None]+list(range(g)):
            degree=_degree(b,p,a)['exact_degree']
            cost=b['core_ledger']['operations']+n+3*m+2*g-1-int(m==0 and g==1 and a==0)
            record=dict(kind=b['kind'],partition=p,anchor=a,operations=cost,exact_degree=degree)
            h.update(canonical_bytes(record)+b'\n');choices+=1
            if cost not in best or degree<best[cost]['exact_degree']:best[cost]=deepcopy(record)
    return dict(kind=b['kind'],partitions=count,finalizer_choices=choices,objective_digest=h.hexdigest(),best_by_cost=[best[k] for k in sorted(best)])

def census(root):
    root=_authenticate(root);data=_parents_cached(str(root.resolve()));families=[_objectives(_rewrite_base(data[k])) for k in KINDS]
    candidates=sorted([r for f in families for r in f['best_by_cost']],key=lambda r:(r['operations'],r['exact_degree'],r['kind']))
    frontier=[];degree=10**9
    for r in candidates:
        if r['exact_degree']<degree:frontier.append(deepcopy(r));degree=r['exact_degree']
    old=json.loads((root/'complete75_asymmetric_linear_gap_tradeoffs.json').read_text())['combined_frontier']
    union=[];bound=10**9
    candidates=[dict(r,coordinate_family='new_ordinary_first_root') for r in frontier]+[dict(r,coordinate_family='frozen_gap_first_root') for r in old]
    for r in sorted(candidates,key=lambda r:(r['operations'],r['exact_degree'],r['coordinate_family'])):
        if r['exact_degree']<bound:union.append(r);bound=r['exact_degree']
    return dict(families=families,frontier=frontier,old_combined_frontier=old,combined_frontier=union,
        partitions=sum(f['partitions'] for f in families),finalizer_choices=sum(f['finalizer_choices'] for f in families),
        scope='Only these13 authenticated bases and binary-product SOS/anchor finalizers; not a general circuit optimum.')

def _dag_cut(rows,cut=True):
    e={}
    for n,op,a,b in rows:
        if cut and n=='norm_first':e[n]=('proven_first_norm_graph_identity',);continue
        def v(x):return ('int',x) if type(x) is int else e.get(x,('free',x))
        e[n]=(op,v(a),v(b))
    return e

def _tops(kind,v):
    Q=v['Bm1']*v['Jrep'];k=v['eta']+v['zeta'];gamma=v['rho']+v['sigma'];w=v['w'];s=v['s'];C=Q-v['F']-v['Z']-v['alpha']-v['twice_cell_bits']*v['x']
    asym=kind.startswith('asymmetric');norm=kind=='asymmetric_normalized';gap=kind.startswith('auxgap')
    if asym:
        return {'norm_first':-(w*s*s*k*Q**7)**2,'norm_main':8*gamma*k*w*w*s**3*Q**11,
            'norm_input':-4*v['delta']**2*w**5*s**5*Q**20,
            'norm_aux':v['i']**2*k**6*w**4*s**10*Q**34 if norm else v['f']**2*k*k*w*w*s**4*Q**14,
            'norm_index':-v['h']*w*s*Q**4,'norm_transport':w*Q*C,
            'norm_strong':-v['i']**2*k**4*w*w*s**6*Q**20 if norm else v['i']**2*k**4*s**4*Q**12,
            'norm_linear':-v['h']*w*s*Q**4,'strong':v['i']**2*k**4*s**4*Q**12}
    uncoupled='uncoupled' in kind or kind.endswith('six_comparisons')
    return {'norm_first':-(w*s*s*k*Q**7)**2,'norm_main':8*gamma*k*w*w*s**3*Q**11,
        'norm_input':4*v['delta']*(2*v['rho']-v['delta'])*w**3*s**3*Q**12,
        'norm_aux':2*v['aux_gap']*v['f']**2*k*w*w*s**3*Q**11 if gap else v['f']**2*k*k*w*w*s**4*Q**14,
        'norm_index':-v['h']*w*s*Q**4,'norm_transport':w*Q*C,
        'norm_strong':v['i']**2*k**4*s**4*Q**12,
        'norm_linear':-v['j']*k*s*Q**3 if uncoupled else -v['h']*w*s*Q**4,
        'strong':v['i']**2*k**4*s**4*Q**12,'linear':v['j']*k*s*Q**3}

def _dense(rows,values,prime):
    def add(a,b,sign):
        c=[((a[i] if i<len(a) else 0)+sign*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))];return trim(c)
    def trim(c):
        while len(c)>1 and c[-1]==0:c.pop()
        return c
    def mul(a,b):
        c=[0]*(len(a)+len(b)-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b):c[i+j]=(c[i+j]+x*y)%prime
        return trim(c)
    e=deepcopy(values)
    for n,op,a,b in rows:
        a=[a%prime] if type(a) is int else e[a];b=[b%prime] if type(b) is int else e[b]
        e[n]=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
    return e

def _fixed(B=16):
    return dict(Bm1=B-1,Kconstant=3+5*B,twice_cell_bits=2*(B.bit_length()-1),inner_bits=3,MC=B-2,MF=B+3)

def verify(root):
    root=_authenticate(root);result=census(root);parents={k:canonical_parent(root,k) for k in KINDS};counts=Counter();rng=random.Random(862026)
    need((result['partitions'],result['finalizer_choices'])==(29631,149336),'Complete finite Bell census')
    need([(r['operations'],r['exact_degree']) for r in result['frontier']]==[(86,179),(87,135),(88,123),(89,119),(90,114),(91,102),(92,80),(93,76),(94,64),(95,54),(96,50),(97,48),(98,44)],'Exact finite family frontier')
    need([(r['operations'],r['exact_degree']) for r in result['combined_frontier']]==[(86,179),(87,135),(88,123),(89,113),(90,109),(91,102),(92,80),(93,72),(94,62),(95,54),(96,50),(97,48),(98,44)],'Union with the complete frozen asymmetric frontier')
    emitted=[];winners=[];degree_records=[]
    # Every best-by-cost plan is emitted and its complete live ledger checked.
    for fam in result['families']:
        b=base(root,fam['kind'])
        for choice in fam['best_by_cost']:
            p=_emit(b,choice['partition'],choice['anchor']);old=_emit(parents[fam['kind']],choice['partition'],choice['anchor'])
            need(p['ledger']['operations']==choice['operations'] and p['degree_certificate']['exact_degree']==choice['exact_degree'],'Literal winner matches objective')
            need(p['ledger']['operations']==old['ledger']['operations']-1 and p['ledger']['M']==old['ledger']['M'],'Every complete finalizer saves one A')
            a=_dag_cut(old['polynomial_source']);bb=_dag_cut(p['polynomial_source'])
            for name in b['factors']+[p['output']]+[v for pair in b['ordinary_comparisons'] for v in pair]:
                need(a[name]==bb[name],'Complete expression-DAG identity after exact first-factor graph cut');counts['complete_DAG_cuts']+=1
            counts['fully_emitted_best_by_cost_plans']+=1
            winners.append(dict(choice,ledger=p['ledger'],equations=p['equations'],certificate_operations=p['certificate_ledger']['operations'],complete_source_sha256=sha(canonical_bytes(p['polynomial_source']))))
            for case in range(8):
                signed=case>=4;v={n:rng.randrange(-3,4) if signed else rng.randrange(1,5) for n in b['witnesses']+['x']};v.update(_fixed(16 if case%2 else 32))
                if case==7:v={n:Fraction(x,2) if n not in CONSTANTS else x for n,x in v.items()}
                now=execute(p['polynomial_source'],v);ov=dict(v);ov['tau_gap']=ov.pop('tau_root')-now['first_root_base'];before=execute(old['polynomial_source'],ov)
                need(now[p['output']]==before[old['output']],'Full inverse graph equality')
                for f in b['factors']:need(now[f]==before[f],'All factor graph identities');counts['factor_graph_identities']+=1
                G=[prod(now[b['factors'][i]] for i in g) for g in p['partition']]
                get=lambda x:x if type(x) is int else now[x]
                S=sum((get(a)-get(bb))**2 for a,bb in b['ordinary_comparisons'])+sum((x-1)**2 for i,x in enumerate(G) if i!=p['anchor'])
                expected=S if p['anchor'] is None else G[p['anchor']]*(1+S)-1
                need(now[p['output']]==expected,'Independent entire manual finalizer')
                counts['complete_numeric_graph_identities']+=1;counts['signed_graph_cases']+=signed;counts['rational_graph_cases']+=case==7
    # Full source coefficients, no leading-term overrides, on two modular affine lines.
    for k in KINDS:
        b=base(root,k)
        for B,prime in [(16,1009),(32,1013)]:
            scales={n:(i%4)+1 for i,n in enumerate(b['witnesses']+['x'])};scales.update(delta=2,rho=5,Jrep=2,x=1)
            topvals=dict(scales,**_fixed(B));tops=_tops(k,topvals)
            vals={n:[i+1,scales[n]] for i,n in enumerate(b['witnesses']+['x'])};vals.update({n:[x] for n,x in _fixed(B).items()})
            e=_dense(b['source'],vals,prime)
            for f,d in zip(b['factors'],b['weights']):
                need(len(e[f])-1==d and e[f][-1]==tops[f]%prime and e[f][-1]!=0,'Actual full factor degree and uniform inherited top form')
                counts['factor_degree_expansions']+=1
            for i,(a,bb) in enumerate(b['ordinary_comparisons']):
                da=e[a];db=e[bb];rr=[((da[j] if j<len(da) else 0)-(db[j] if j<len(db) else 0))%prime for j in range(max(len(da),len(db)))];
                while len(rr)>1 and rr[-1]==0:rr.pop()
                name='strong' if i==0 else 'linear'
                need(len(rr)-1==b['residual_degrees'][i] and rr[-1]==tops[name]%prime,'Actual retained residual degree')
                counts['retained_residual_degree_expansions']+=1
            degree_records.append(dict(kind=k,B=B,prime=prime,factor_leading_coefficients=[e[f][-1] for f in b['factors']]))
    for choice in result['frontier']:
        p=build(root,choice['kind'],choice['partition'],choice['anchor']);emitted.append(p)
        for B,prime in [(16,1009),(32,1013)]:
            b=p['base'];s={n:(i%4)+1 for i,n in enumerate(b['witnesses']+['x'])};s.update(delta=2,rho=5,Jrep=2,x=1)
            vals={n:[i+1,s[n]] for i,n in enumerate(b['witnesses']+['x'])};vals.update({n:[x] for n,x in _fixed(B).items()})
            e=_dense(p['polynomial_source'],vals,prime);d=p['degree_certificate'];need(len(e[p['output']])-1==d['exact_degree'],'Complete literal univariate degree attained')
            tops=_tops(b['kind'],dict(s,**_fixed(B)));gt=[prod(tops[b['factors'][i]] for i in g) for g in p['partition']]
            res=[(deg,tops['strong' if i==0 else 'linear']) for i,deg in enumerate(b['residual_degrees'])]+[(deg,gt[i]) for i,deg in enumerate(d['group_degrees']) if i!=p['anchor']]
            r=max([0]+[dd for dd,_ in res]);lead=sum(c*c for dd,c in res if dd==r) if res else 1
            if p['anchor'] is not None:lead*=gt[p['anchor']]
            need(e[p['output']][-1]==lead%prime and lead%prime!=0,'Complete top coefficient agrees with proved product/SOS expression')
            counts['complete_dense_degree_expansions']+=1
    known=json.loads((root/'complete86_factored_first_root.json').read_text())['forms']
    for p,r in zip(emitted[:2],known):
        need(_dag_cut(p['polynomial_source'],False)[p['output']]==_dag_cut(r['source'],False)[r['output']],'Exact complete86/87 emitted source polynomial reproduced')
        counts['complete86_87_full_DAG_matches']+=1
    # Exact local first-root identity, expanded in independent T,L,k atoms.
    def poly_add(a,b,sign=1):
        c=Counter(a)
        for m,v in b.items():c[m]+=sign*v
        return {m:v for m,v in c.items() if v}
    def poly_mul(a,b):
        c=Counter()
        for m,v in a.items():
            for n,w in b.items():c[tuple(x+y for x,y in zip(m,n))]+=v*w
        return dict(c)
    T={(1,0,0):1};L={(0,1,0):1};k={(0,0,1):1};g=poly_add(T,L,-1)
    old=poly_add(poly_mul(g,g),poly_mul(L,poly_add(poly_add(g,g),k,-1)))
    new=poly_add(poly_mul(T,T),poly_mul(L,poly_add(L,k)),-1)
    need(old==new,'All-value ordinary-root norm expansion');counts['symbolic_local_graph_identity']=1
    signs=set()
    for L in range(1,65):
        for k in range(2,33):
            for eps in [-1,1]:
                n=L*L+L*k+eps;T=isqrt(n)
                if T*T==n:need(T>L,'Positive inverse before any parent theorem');signs.add(eps);counts['both_sign_inverse_fixtures']+=1
    need(signs=={-1,1},'Both unit signs covered')
    # Strict canonical packets include all metadata; numeric aliases cannot pass.
    for p in emitted:
        k=p['base']['kind'];parent=parents[k]
        for target in ['child','parent']:
            original=p if target=='child' else parent
            bad=[]
            # Mutations common to all nested shapes are generated recursively.
            def paths(x,path=()):
                if type(x) is dict:
                    for key,v in x.items():yield from paths(v,path+(key,))
                elif type(x) is list:
                    for i,v in enumerate(x):yield from paths(v,path+(i,))
                elif type(x) is int:yield path,x
            for path,v in list(paths(original))[:18]:
                for replacement in (float(v),bool(v),v+1):
                    x=deepcopy(original);a=x
                    for t in path[:-1]:a=a[t]
                    a[path[-1]]=replacement;bad.append(x)
            x=deepcopy(original);x['unexpected']=True;bad.append(x)
            for x in bad:
                try:checked(root,x) if target=='child' else base(root,k,x)
                except (ValueError,TypeError,KeyError):counts['malformed_packet_rejections']+=1
                else:raise AssertionError('Malformed canonical packet accepted')
        vals={n:1 for n in p['base']['witnesses']+['x']};vals.update(_fixed())
        need(evaluate(root,p,vals)==execute(p['polynomial_source'],vals)[p['output']],'Guarded public evaluation')
        parentvals={n:1 for n in parent['witnesses']+['x']};parentvals.update(_fixed())
        lifted=coordinate(root,p,parentvals,positive=True);need(coordinate(root,p,lifted,to_parent=True,positive=True)==parentvals,'Public positive forward graph roundtrip')
        for flag in [0,1,None,'False']:
            try:evaluate(root,p,vals,signed=flag)
            except ValueError:counts['domain_flag_rejections']+=1
            else:raise AssertionError('NonBoolean flag accepted')
        for badval in [True,1.0,0,-1]:
            v=dict(vals,tau_root=badval)
            try:evaluate(root,p,v)
            except ValueError:counts['coordinate_type_domain_rejections']+=1
            else:raise AssertionError('Bad positive coordinate accepted')
        for badpart,a in [(p['partition'],True),([],None),([[0],[0]],None),([list(range(len(p['base']['factors'])))[::-1]],None)]:
            try:build(root,k,badpart,a)
            except ValueError:counts['malformed_plan_rejections']+=1
            else:raise AssertionError('Malformed plan accepted')
        for bad in (p['base'],p,dict(parent,source=p['base']['source'])):
            try:base(root,k,bad)
            except ValueError:counts['no_op_or_wrong_parent_rejections']+=1
            else:raise AssertionError('No-op or child accepted as parent')
        try:coordinate(root,p,vals,to_parent=True,positive=True)
        except ValueError:counts['positive_offzero_inverse_rejections']+=1
        else:raise AssertionError('Invalid positive inverse accepted')
        independent=build(root,k,p['partition'],p['anchor']);independent['base']['weights'][0]=999
        need(build(root,k,p['partition'],p['anchor'])['base']['weights'][0]!=999,'No exposed mutable cache');counts['defensive_copy_checks']+=1
    with tempfile.TemporaryDirectory(prefix='first-root-pins-') as temporary:
        sandbox=Path(temporary)
        for name in PINS:(sandbox/name).write_bytes((root/name).read_bytes())
        canonical_parent(sandbox)
        for name in ['complete75_asymmetric_scale_tradeoffs.json','complete75_asymmetric_linear_gap_tradeoffs.py']:
            original=(sandbox/name).read_bytes();(sandbox/name).write_bytes(original+b' ')
            try:canonical_parent(sandbox)
            except ValueError:counts['warm_cache_source_pin_rejections']+=1
            else:raise AssertionError('Warm cache bypassed parent pin')
            (sandbox/name).write_bytes(original)
        _parents_cached.cache_clear()
    return dict(status='PASS_COMPLETE_FIRST_ROOT_FINITE_PARTITIONS',source_sha256=sha(Path(__file__).read_bytes()),parent_pins=PINS,
        census=result,winner_ledgers=winners,frontier_sources=emitted,degree_component_receipts=degree_records,counts=dict(counts),
        scope='Finite13-base family; all ordinary input/program/domain/native obligations retained. Complete positive-zero bijections, not all-positive-tuple inverse maps. No full accepting Pell tuple constructed. Exact degrees inherit pinned uniform parent leading forms plus the proved new first-factor leading form.')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);args=ap.parse_args()
    result=verify(args.root);raw=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:args.output.write_text(raw)
    target=args.expect if args.expect else (None if args.output else Path(__file__).with_suffix('.json'))
    if target:need(exact(json.loads(raw),json.loads(target.read_text())),'Fresh typed receipt equals saved receipt')
    print(json.dumps({'status':result['status'],'frontier':[(r['operations'],r['exact_degree']) for r in result['census']['frontier']],'counts':result['counts']},sort_keys=True))
if __name__=='__main__':main()

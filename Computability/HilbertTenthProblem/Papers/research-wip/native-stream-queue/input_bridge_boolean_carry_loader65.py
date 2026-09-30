"""Exact hidden-carry erasure, odd cycle, and one-addition ordinary-input marker."""
import argparse
from collections import Counter, deque
from itertools import product
import hashlib
import json
from pathlib import Path
import sympy as sp

import native_controller_boolean_carry70 as prior


def source_check(controller=True, aligned=False, symmetric=False):
    base = prior.source_check(controller, aligned, symmetric)
    schedule = []
    for name,op,left,right in base['instructions']:
        if name == 'bt_initial':
            assert (op,left,right) == ('*',2,'x')
            schedule += [(name,'*',6,'x'),('loader_initial','+',name,2)]
        else:
            schedule.append((name,op,'loader_initial' if left=='bt_initial' else left,
                             'loader_initial' if right=='bt_initial' else right))
    names = base['positive_parameters']+base['positive_auxiliaries']
    z = {name:sp.Symbol(name) for name in names}
    fixed = {name:sp.Symbol(name) for name in ('g0','g1','g2','gap')}
    env = prior.boolean.prior.execute(schedule,dict(z,**fixed,n2=z['q']))
    records=[]
    for record in base['sources']:
        left,right=record['equality']
        left='loader_initial' if left=='bt_initial' else left
        right='loader_initial' if right=='bt_initial' else right
        polynomial=sp.expand(sp.sympify(record['source'],locals=dict(z,**fixed)).subs(z['x'],3*z['x']+1))
        correction=sp.sympify(record['correction'],locals=dict(z,**fixed))
        assert z['x'] not in correction.free_symbols
        assert sp.expand(env[left]-env[right]-polynomial-correction)==0
        records.append(dict(equality=[left,right],source=str(polynomial),correction=str(correction)))
    counts=Counter(row[1] for row in schedule)
    assert len(schedule)==base['operations']+1
    assert counts['*']==base['multiplications']
    assert counts['+']+counts['-']==base['additions_subtractions']+1
    assert len(records)==19+controller+2*aligned and len(names)-1==29+2*aligned
    assert sp.sympify(records[14]['source'],locals=z)==6*z['x']+2+z['width_beta']-z['W']
    assert sp.sympify(records[16]['source'],locals=z)==z['init0']+z['init1']-6*z['x']-2
    return dict(operations=len(schedule),multiplications=counts['*'],
                additions_subtractions=counts['+']+counts['-'],equations=len(records),
                positive_witnesses_excluding_x=len(names)-1,
                positive_parameters=base['positive_parameters'],positive_auxiliaries=base['positive_auxiliaries'],
                fixed_constants=base['fixed_constants'],alignment=base['alignment'],
                instructions=[list(row) for row in schedule],sources=records,
                initial_value='6*x+2',scope='Exact positive finite-machine component, not a universal compiler')


TABLE = {(0,0):[(1,0)],(0,1):[(1,0)],(0,2):[(0,0),(2,1)],
         (1,0):[(1,0)],(1,1):[(0,0),(2,1)],(1,2):[(1,1)]}


class Trace:
    def __init__(self, n, m):
        assert 0<=n<3**m
        self.queue=list(prior.digits(n,m));self.e=0;self.rows=[];self.m=m

    def step(self, appended, next_e):
        read=self.queue[0]
        assert (appended,next_e) in TABLE[self.e,read]
        pairs=[(a0,a1) for a0,a1 in product((0,1),repeat=2)
               if a0+a1==appended and self.e+2*a0+a1+read-2==3*next_e]
        assert len(pairs)==1
        self.rows.append((pairs[0][0],pairs[0][1],read,self.e,next_e))
        self.queue=self.queue[1:]+[appended];self.e=next_e


def odd_loop(trace):
    m=trace.m
    assert m>=3 and trace.e==0 and trace.queue==[2]+[1]*(m-1)
    start=len(trace.rows)
    trace.step(2,1);trace.step(2,1);trace.step(0,0)
    for _ in range(m-3):trace.step(1,0)
    assert trace.queue==[2,2,0]+[1]*(m-3) and trace.e==0
    trace.step(0,0);trace.step(2,1);trace.step(1,0)
    for _ in range(m-3):trace.step(1,0)
    assert trace.queue==[0,2]+[1]*(m-2) and trace.e==0
    trace.step(1,0)
    assert trace.queue==[2]+[1]*(m-1) and trace.e==0
    assert len(trace.rows)-start==2*m+1


def erase(n,m,even=False):
    trace=Trace(n,m)
    assert 2 in trace.queue
    assert not even or (m>=4 and m%2==0)
    if m==1:
        trace.step(2,1);trace.step(1,1);trace.step(0,0)
    else:
        j=max(i for i,d in enumerate(trace.queue) if d==2)
        for _ in range(j):trace.step(0 if trace.queue[0]==2 else 1,0)
        trace.step(2,1)
        assert trace.queue[-1]==2 and all(d in (0,1) for d in trace.queue[:-1])
        b=trace.queue[0];trace.step(1-b,0)
        for _ in range(m-2):trace.step(1,0)
        assert trace.queue==[2,1-b]+[1]*(m-2) and trace.e==0
        if b:
            trace.step(2,1);trace.step(1,0)
            for _ in range(m-2):trace.step(1,0)
        assert trace.queue==[2]+[1]*(m-1) and trace.e==0
        assert len(trace.rows)<=3*m-1
        if even and (len(trace.rows)+2*m-1)%2:odd_loop(trace)
        trace.step(2,1)
        for _ in range(m-2):trace.step(2,1)
        trace.step(0,0)
        for _ in range(m-1):trace.step(0,0)
    assert trace.e==0 and trace.queue==[0]*m
    assert m<len(trace.rows)<=(7*m-1 if even else 5*m-2)
    assert not even or len(trace.rows)%2==0
    assert any(row[:2]==(1,1) for row in trace.rows)
    return trace


def physical_map(I,m,even=False):
    assert I>0 and I%2==0
    trace=erase(I,m,even)
    I0,I1=prior.paired.positive_split(I)
    assert I0>0 and I1>0
    n0,n1=I0,I1;e=0;labels=[]
    for a0,a1,r,old_e,new_e in trace.rows:
        d0,d1=n0%3,n1%3
        assert d0+d1==r and old_e==e
        label=(a0,a1,d0,d1)
        assert prior.hidden_step(e,label)==new_e
        e=new_e;labels.append(label)
        n0,n1=n0//3+3**(m-1)*a0,n1//3+3**(m-1)*a1
    assert n0==n1==e==0
    t=len(labels);W,q=3**m,3**t
    fields=[prior.word(row[i] for row in labels) for i in range(4)]
    assert min(fields)>0 and all(prior.boolean.native_boolean(f,t) for f in fields)
    assert fields[2]==I0+W*fields[0] and fields[3]==I1+W*fields[1]
    assert 2*fields[0]+sum(fields[1:])==q-1
    assert sum(fields)%2==0 and q-sum(fields)==fields[0]+1>0
    assert 0<I<W and t>m and q%W==0
    if even:assert m%2==t%2==0
    return dict(initial_value=I,m=m,t=t,W=W,q=q,initial=[I0,I1],fields=fields,
                alpha=fields[0]+1,width_beta=W-I,L=q//W,
                time_root=(3**(t//2) if even else None),width_root=(3**(m//2) if even else None))


def exhaustive_constructions():
    rows=[]
    for m in range(1,8):
        words=positive_even=0;longest=0
        for I in range(1,3**m):
            if 2 not in prior.digits(I,m):continue
            trace=erase(I,m)
            longest=max(longest,len(trace.rows));words+=1
            if I%2==0:
                physical_map(I,m);positive_even+=1
        rows.append(dict(width=m,scalar_words=words,positive_even_physical_maps=positive_even,
                         maximum_constructed_time=longest,proved_time_bound=5*m-2))
    for m in range(3,101):
        trace=Trace(prior.word([2]+[1]*(m-1)),m);odd_loop(trace)
    return dict(domains=rows,total_scalar_constructions=sum(r['scalar_words'] for r in rows),
                positive_even_physical_maps=sum(r['positive_even_physical_maps'] for r in rows),
                explicit_odd_cycles=98,scope='The direct constructive algorithm and its physical positive lift; no guessed controller')


def finite_basins():
    rows=[]
    for m in range(1,8):
        W=3**m;incoming=[[] for _ in range(2*W)]
        for n in range(W):
            for e in (0,1):
                for a,b in TABLE[e,n%3]:
                    nxt=n//3+(W//3)*a
                    incoming[2*nxt+b].append(2*n+e)
        seen={0};pending=deque([0])
        while pending:
            nxt=pending.popleft()
            for old in incoming[nxt]:
                if old not in seen:seen.add(old);pending.append(old)
        for n in range(W):
            assert (2*n in seen)==(n==0 or 2 in prior.digits(n,m))
        rows.append(dict(width=m,complete_scalar_configurations=2*W,
                         zero_reachable_configurations=len(seen),state_zero_words=W))
    return dict(domains=rows,scope='Complete finite graph cross-check of the proved hidden-state-zero basin; no unproved classification of state-one words is used')


def ordinary_maps():
    examples=[];aligned=0
    for x in range(1,201):
        I=6*x+2
        assert I%3==2 and I%2==0
        for even in (False,True):
            m=4 if even else 1
            while 3**m<=I:m+=2 if even else 1
            result=physical_map(I,m,even)
            if even:aligned+=1
            if x in (1,2,10,200):examples.append(dict(x=x,aligned=even,**result))
    return dict(ordinary_positive_inputs=200,all_positive_outer_maps=400,
                even_width_and_time_maps=aligned,examples=examples,
                external_controller='Zero controller accepts these examples; no arbitrary nonzero-controller completeness is claimed',
                full_kernel_extension='Proved parametrically by the exact positive Boolean/Pell converse, not materialized')


def verify():
    return dict(status='PASS_BOOLEAN_CARRY_MARKER65_AND_CONSTRUCTIVE_ERASURE',
                sources=dict(bare65=source_check(False),symmetric68=source_check(symmetric=True),
                             controller71=source_check(),aligned73=source_check(aligned=True)),
                construction=exhaustive_constructions(),finite_basins=finite_basins(),ordinary_maps=ordinary_maps(),
                dependency_sha256=hashlib.sha256(Path(prior.__file__).read_bytes()).hexdigest(),
                theorem='The bare raw64 language is exactly those x with a trit2 in2x; paid input6x+2 gives all positive inputs, including even width and duration',
                scope='Complete components and explicit positive histories, not a universal external-controller compiler',
                established_complete_universal_bound=76)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();receipt=Path(__file__).with_suffix('.json')
    if args.write:receipt.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(receipt.read_text())==result,'receipt mismatch'
    print(json.dumps({k:v for k,v in result.items() if k not in ('sources','ordinary_maps')},indent=2))

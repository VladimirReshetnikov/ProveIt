"""Audit executable for finite candidate slots and the total-event scheduler.
Not the arbitrary-mass polynomial exporter. Loads exactly the pinned evaluator.
"""
from pathlib import Path
from hashlib import sha256
import sys, importlib.util
P=Path(__file__).resolve().with_name('lazy_reversible.py')
HASH='42e8aa65c05fcf373a03a02be51ebb89a4fdcb1f1070ad776ffe1e8e99049c61'
if sha256(P.read_bytes()).hexdigest()!=HASH:raise RuntimeError('Changed evaluator')
spec=importlib.util.spec_from_file_location('_pinned_lazy_step_schema',P)
lazy=importlib.util.module_from_spec(spec);sys.modules[spec.name]=lazy;spec.loader.exec_module(lazy)

def slots(a,positions):
    x=tuple(sorted(positions));n=len(x);result=[]
    delta=max([0]+[len(v) for v in a.home_out.values()]+[len(v) for v in a.home_in.values()])
    es,em,pm,r=4*a.D+15,2*a.D+6,2*a.D+7,a.D+3
    for i in range(n):
        for j in range(i+1,n):
            h=x[i];d=x[j]-h;home=1<=d<=2*a.m;moving=2*a.m<d<=a.D
            positive=d%2==1;marker=h-a.S in positions;qi=(d-1)//2 if home else 0
            def put(flag,index):result.append((bool(flag),index if flag else a.factors))
            put(home and marker,a.E_count+2*a.p*pm+qi)
            incident=(a.home_out if positive else a.home_in).get(qi,()) if home and marker else ()
            for rank in range(delta):put(rank<len(incident),incident[rank] if rank<len(incident) else 0)
            mode_no,offset=divmod(d-2*a.m-1,4) if moving else (0,0)
            kind=offset//2;side=a.moving[mode_no].side if moving else 1;w=side if kind==0 else -side
            eb=mode_no*es+kind*em;pb=a.E_count+(2*mode_no+kind)*pm
            put(moving,eb);put(moving,pb)
            for k,z in enumerate(x):
                if k in (i,j):continue
                distance=h-z;t=w*distance-(0 if positive else 1)
                put(moving and a.S<=t<=a.L,eb+1+t-a.S)
                t=-w*distance+(0 if positive else 1)
                put(moving and a.S+1<=t<=a.L,eb+1+r+t-(a.S+1))
                t=abs(distance);side_no=0 if distance<0 else 1
                put(moving and a.S<=t<=a.L,pb+1+side_no*r+t-a.S)
                interaction=None
                if kind==0 and positive and distance==-side*a.S:interaction=1
                if kind==0 and not positive and distance==side*a.S:interaction=0
                if kind==1 and positive and distance==side*a.S:interaction=2
                if kind==1 and not positive and distance==-side*a.S:interaction=1
                put(moving and interaction is not None,mode_no*es+2*em+(interaction or 0))
    expected=n*(n-1)//2*(delta+3+4*max(n-2,0))
    if len(result)!=expected:raise RuntimeError(('slot count',len(result),expected))
    return result

def next_change(a,x,cursor):
    best=None
    # All distinct candidate effects are pure functions of the same pre-factor x.
    cache={}
    for rank,(enabled,index) in enumerate(slots(a,x)):
        if not enabled:continue
        if index not in cache:cache[index]=lazy.apply_gate(a.gate_at(index),x)[0]
        y=cache[index]
        if index>=cursor and y!=x and (best is None or (index,rank)<best[:2]):best=(index,rank,y)
    return best

def run(a,positions,T,K):
    if any(type(v) is not int or v<0 for v in (T,K)):raise ValueError('budgets')
    x=frozenset(positions);t=0;cursor=0;records=[]
    for round_no in range(T+K):
        found=next_change(a,x,cursor) if t<T else None
        if t==T:kind='idle'
        elif found is None:t+=1;cursor=0;kind='complete'
        else:cursor=found[0]+1;x=found[2];kind='change'
        records.append(dict(round=round_no,kind=kind,time=t,cursor=cursor,index=found[0] if found else None,support=sorted(x)))
    return t==T,x,records

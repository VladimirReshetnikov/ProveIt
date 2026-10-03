#!/usr/bin/env python3
"""Independent complete-circuit audit of the five-natural-coordinate atom."""
import argparse
from collections import Counter
import hashlib
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

PIN='f33ba14f16009f4e825e00a91d1714696dadf34002ada3bf72fcbccc04a52cfc'

def need(ok,msg):
    if not ok:raise ValueError(msg)
def exact(a,b):
    if type(a) is not type(b):return False
    if type(a) is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if type(a) in (list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b

def run(c,v):
    env=dict(v);free=set(c['inputs']);seen=set(free)
    for name,op,a,b in c['gates']:
        need(name not in seen,'Repeated register')
        args=[]
        for arg in (a,b):
            if type(arg) is int:args.append(arg)
            else:need(type(arg) is str and arg in seen,'Open DAG');args.append(env[arg])
        need(op in ('add','sub','mul'),'Unknown gate')
        aa,bb=args;env[name]=aa+bb if op=='add' else aa-bb if op=='sub' else aa*bb;seen.add(name)
    need(c['output'] in seen and all(r in seen for r in c['rows']),'Missing output')
    return env[c['output']],tuple(env[r] for r in c['rows'])

def verify(source):
    import sympy as sp
    path=Path(source);need(hashlib.sha256(path.read_bytes()).hexdigest()==PIN,'Pinned atom source differs')
    name='_independent_presburger_atom';old=sys.modules.pop(name,None)
    try:
        spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);sys.modules[name]=m;spec.loader.exec_module(m)
        count=Counter();L,qp,qm,b,s,h,a=sp.symbols('L qp qm b s h a');env=dict(zip(('L','qp','qm','b','s','h','a'),(L,qp,qm,b,s,h,a)));records=[]
        for d in (1,2,3,7,10**100+267):
            child,parent=m.build(d),m.build(d,True);F,rows=run(child,env);G,oldrows=run(parent,env)
            target=(qp*qm,L-d*(qp-qm)-b*(s+1),b*(s+1)+h-d+1,b*(b-1),(b-1)*s)
            need(all(sp.expand(x-y)==0 for x,y in zip(rows,target)),'Actual child row mismatch');count['complete_literal_rows']+=5
            restored=tuple(sp.expand(r.subs(a,b*(s+1))) for r in oldrows)
            need(all(sp.expand(restored[i]-rows[i])==0 for i in range(4)) and sp.expand(restored[4]+rows[4])==0,'Full graph row mapping');count['all_value_graph_row_maps']+=5
            need(sp.expand(G.subs(a,b*(s+1))-F)==0,'Complete all-value graph SOS identity');count['all_value_complete_SOS_identities']+=1
            need(sp.Poly(F,*env.values()).total_degree()==4,'Wrong exact degree');count['exact_quartic_degrees']+=1
            for c,expected in ((child,(9,12,21)),(parent,(9,13,22))):
                mul=sum(row[1]=='mul' for row in c['gates']);adds=len(c['gates'])-mul
                need((mul,adds,len(c['gates']))==expected,'Independent actual ledger differs');count['complete_charged_ledgers']+=1
            records.append(dict(modulus=str(d),child=[9,12,21],parent=[9,13,22],degree=4))
        # The search includes every possible natural root in this box: qp,qm<=13
        # for |L|<=12; b<=1 follows its own row, and s,h<d from the range rows.
        for d,Lv in product(range(1,8),range(-12,13)):
            expected=m.canonical(Lv,d);roots=[]
            for qpv,qmv in product(range(14),repeat=2):
                if qpv*qmv:continue
                for bv,sv,hv in product(range(2),range(d),range(d)):
                    W=(qpv,qmv,bv,sv,hv)
                    if qpv*qmv==0 and Lv-d*(qpv-qmv)-bv*(sv+1)==0 and bv*(sv+1)+hv-d+1==0 and bv*(bv-1)==0 and (1-bv)*sv==0:roots.append(W)
            need(roots==[expected],'Independent complete natural-fibre census');count['complete_small_fibres']+=1
            need(1-expected[2]==int(Lv%d==0),'Wrong divisibility bit');count['truth_bits']+=1
        for d in (1,3,17):
            child,parent=m.build(d),m.build(d,True)
            for j in range(40):
                values={n:((j+3)*(i+5)%19)-9 for i,n in enumerate(('L','qp','qm','b','s','h'))};restored=dict(values,a=values['b']*(values['s']+1))
                need(run(child,values)[0]==run(parent,restored)[0],'Signed integer graph check');count['signed_graph_evaluations']+=1
        for bad in ((True,2),(0,False),(0,1.0),(1.0,2),(0,0),(0,-2)):
            try:m.canonical(*bad)
            except ValueError:count['invalid_domain_rejections']+=1
            else:raise ValueError('Invalid exact integer/modulus accepted')
    finally:
        sys.modules.pop(name,None)
        if old is not None:sys.modules[name]=old
    return dict(status='PASS_INDEPENDENT_CONGRUENCE_ATOM',source_sha256=PIN,counts=dict(count),ledgers=records,
                scope='Five natural auxiliary coordinates, five quadratic rows, unique complete natural fibre for every signed L and fixed d>=1. Exact all-value graph SOS identity with displayed six-coordinate parent. L evaluation and outer Boolean/final accumulation excluded from atom counts, no optimality or universal operation claim.')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--source',type=Path,required=True);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args();out=verify(a.source)
    if a.expect:need(exact(out,json.loads(a.expect.read_text())),'Review receipt differs')
    if a.output:a.output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(out,indent=2,sort_keys=True))

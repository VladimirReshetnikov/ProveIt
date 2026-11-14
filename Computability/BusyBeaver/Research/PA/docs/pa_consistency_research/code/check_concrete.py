#!/usr/bin/env python3
"""Exact concrete root-frame comparisons for a supplied source/candidate pair.

All input/output tapes are finite sets of 1 positions, so the omitted exterior
is exactly zero. A wrong first clean canonical root is recorded as a macro
mismatch. This does not decide blank-tape halting equivalence.
"""
import sys,json,argparse,hashlib
from pathlib import Path
HERE=Path(__file__).resolve().parent;BASE=HERE/'runtime'
sys.path.insert(0,str(BASE));import independent_runtime as r,source_language as s

def frame(pc,registers,spares,gap,head=0):
    bits={head-1,head+gap};bits.update(head+i for i,b in enumerate(pc) if b=='1')
    physical=[None]*9
    for i,j in enumerate(r.PHY):physical[j]=registers[i]
    pos=head+gap+1
    for value in physical+spares:
        pos+=1;bits.update(range(pos,pos+value+1));pos+=value+1
    return bits

def expectation(site,values,spares,gap):
    pc,op,arg=site;out=values.copy();extra=spares.copy();delta=0;overflow=0
    if op=='CI':out[arg]+=1;successor,overflow=r.inc(pc);extra.append(1)
    elif op=='CD' and values[arg]>0:out[arg]-=1;successor,overflow=r.inc(pc);delta=1
    elif op in ('CD','CB'):successor,overflow=r.inc(r.strip(pc,'0',1 if op=='CD' else arg))
    elif op=='CC':successor=r.strip(pc,'1',arg)
    else:raise ValueError(site)
    return dict(pc=successor,registers=out,spares=extra,gap=gap+delta+overflow,head=-overflow)

def parse_frame(bits,head,tree,min_gap):
    if head-1 not in bits or any(x<head-1 for x in bits):return None
    n=tree;pc='';pos=head
    while not s.leaf(n):
        bit=int(pos in bits);pc+=str(bit);n=n[bit];pos+=1
    after=[x for x in bits if x>=pos]
    if not after:return None
    header=min(after)
    if header-head<min_gap:return None
    last=max(bits);pos=header+1;physical=[]
    while pos<=last:
        if pos in bits:return None
        pos+=1;start=pos
        while pos in bits:pos+=1
        if start==pos:return None
        physical.append(pos-start-1)
    if len(physical)<10:return None
    values=[physical[j] for j in r.PHY]
    return dict(pc=pc,registers=values,spares=physical[9:],gap=header-head,head=head)

def run(table,initial,expected,tree,gap,bound):
    q=84;head=0;bits=initial.copy();roots=[];seen={}
    expectedbits=frame(**expected)
    for i in range(1,bound+1):
        if q==254:return dict(status='HALT',steps=i-1,head=head,ones=sorted(bits),root_visits=roots)
        key=(q,head,tuple(sorted(bits)))
        if key in seen:return dict(status='LOOP',steps=i-1,loop_start=seen[key],head=head,state=q,ones=sorted(bits),root_visits=roots)
        seen[key]=i-1
        w,d,q=table[q,int(head in bits)]
        if w:bits.add(head)
        else:bits.discard(head)
        head+=d
        if q==84:
            if len(roots)<30:roots.append([i,head])
            if head==expected['head'] and bits==expectedbits:
                return dict(status='EXPECTED_TARGET',steps=i,root_visits=roots,actual=expected,ones=sorted(bits))
            parsed=parse_frame(bits,head,tree,gap)
            if parsed is not None:
                return dict(status='OTHER_CLEAN_ROOT',steps=i,root_visits=roots,actual=parsed,ones=sorted(bits))
    return dict(status='BOUND',steps=bound,head=head,state=q,ones=sorted(bits),root_visits=roots)

def main():
    p=argparse.ArgumentParser();p.add_argument('--machine',type=Path,required=True);p.add_argument('--source',type=Path,required=True)
    p.add_argument('--index',type=int,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--bound',type=int,default=100000)
    a=p.parse_args();table=r.table(a.machine);sites=json.loads(a.source.read_text());tree=s.tree(sites);site=sites[a.index]
    tests=[[0]*9]
    for reg in range(9):
        for v in (1,2,3):x=[0]*9;x[reg]=v;tests.append(x)
    results=[]
    for gap in (48,56):
        for values in tests:
            expected=expectation(site,values,[0],gap);initial=frame(site[0],values,[0],gap)
            result=run(table,initial,expected,tree,gap,a.bound)
            results.append(dict(initial_pc=site[0],initial_registers=values,initial_spares=[0],initial_gap=gap,
                                initial_ones=sorted(initial),expected=expected,expected_ones=sorted(frame(**expected)),**result))
            print(gap,values,result['status'],result['steps'],result.get('actual'),flush=True)
    report=dict(machine=str(a.machine),machine_sha256=hashlib.sha256(a.machine.read_bytes()).hexdigest(),
                source_sha256=hashlib.sha256(a.source.read_bytes()).hexdigest(),site_index=a.index,site=site,results=results,
                scope='Exact concrete traces to first clean canonical root, expected target, halt, loop, or finite bound. A finite macro mismatch does not settle blank-tape halting equivalence.')
    a.output.write_text(json.dumps(report,indent=2)+'\n')

if __name__=='__main__':main()

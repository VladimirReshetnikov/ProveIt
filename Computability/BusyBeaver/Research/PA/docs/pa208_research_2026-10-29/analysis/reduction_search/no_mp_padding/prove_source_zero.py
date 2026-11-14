#!/usr/bin/env python3
"""Check an unbounded zero invariant by finite abstract induction.

Domains at each ordinal are products of {0}, positive naturals, or all naturals.
The checker verifies initial inclusion and every nonempty branch image. Thus a
passed certificate is an inductive invariant, not a bounded execution test.
Python standard library only. CFG resolution uses independent subtree intervals.
"""
from pathlib import Path
import argparse,collections,hashlib,json

MASK=511
SOURCE_SHA256='cddbed7f20e7a8b085b7ca0e76811d07b021522375643b5d1134eec0d2d23164'
ROOT=Path(__file__).resolve().parents[3]
DEFAULT_SOURCE=ROOT/'upstream/u208_research_2026-10-29/u208_research_2026-10-29/machine/variant_plain/u208.sites.json'
BOOTSTRAP=[1,0,13,0,0,1,0,0,1]

def graph_intervals(rows):
    """Resolve tree-relative branches, retaining the source's root wraparound."""
    n=len(rows);leaves={p:i for i,(p,_,_) in enumerate(rows)};intervals={}
    if len(leaves)!=n:raise ValueError('Duplicate source addresses')
    def visit(p):
        if p in leaves:result=(leaves[p],leaves[p]+1)
        else:
            a,b=visit(p+'0'),visit(p+'1')
            if a[1]!=b[0]:raise ValueError('Noncontiguous source subtree')
            result=(a[0],b[1])
        intervals[p]=result;return result
    if visit('')!=(0,n):raise ValueError('Invalid tree census')
    def branch(path,bit,level):
        for k in range(len(path)-1,-1,-1):
            if path[k]==bit:
                level-=1
                if level==0:
                    a,b=intervals[path[:k]]
                    return (b if bit=='0' else a)%n
        return 0
    graph=[]
    for i,(p,op,a) in enumerate(rows):
        if op=='CI':targets=[(i+1)%n]
        elif op=='CD':targets=[branch(p,'0',1),(i+1)%n]
        elif op=='CB':targets=[branch(p,'0',a)]
        elif op=='CC':targets=[branch(p,'1',a)]
        elif op=='CH':targets=[]
        else:raise ValueError('Unknown opcode')
        graph.append(targets)
    return graph

def images(row,targets,domain):
    z,p=domain;_,op,a=row
    if op=='CH':return []
    if op=='CI':return [(targets[0],(z&~(1<<a),p|(1<<a)))]
    if op=='CD':
        b=1<<a;out=[]
        if not p&b:out.append((targets[0],(z|b,p&~b)))
        if not z&b:out.append((targets[1],(z&~b,p&~b)))
        return out
    return [(targets[0],domain)]

def derive(rows,graph):
    domains=[None]*len(rows);domains[0]=(MASK^1,1);queue=collections.deque([0])
    while queue:
        i=queue.popleft()
        for j,out in images(rows[i],graph[i],domains[i]):
            prior=domains[j]
            joined=out if prior is None else (prior[0]&out[0],prior[1]&out[1])
            if prior!=joined:domains[j]=joined;queue.append(j)
    return domains

def verify(rows,graph,domains):
    if len(domains)!=len(rows):raise ValueError('Wrong domain count')
    initial=(MASK^1,1);z,p=domains[0]
    if z&~initial[0] or p&~initial[1]:raise ValueError('Initial source state excluded')
    z,p=domains[136]
    for k,v in enumerate(BOOTSTRAP):
        if (z>>k&1 and v) or (p>>k&1 and not v):raise ValueError('Calibrated bootstrap store excluded')
    edges=0
    for i,dom in enumerate(domains):
        if dom is None:continue
        z,p=dom
        if z&p or (z|p)&~MASK:raise ValueError('Malformed domain')
        for j,out in images(rows[i],graph[i],dom):
            if domains[j] is None:raise ValueError('Reachable edge into excluded ordinal')
            tz,tp=domains[j]
            if tz&~out[0] or tp&~out[1]:raise ValueError(f'Noninductive edge {i}->{j}')
            edges+=1
    if not domains[3847][0]&(1<<1):raise ValueError('T=0 at MP success was not established')
    if domains[3848] is not None or domains[3849] is not None:raise ValueError('Dead transfer body unexpectedly reachable')
    return {'checked_edges':edges,'inductive_domain_count':sum(d is not None for d in domains),
            'target_ordinal':3847,'T_always_zero':True,'dead_ordinals':[3848,3849],
            'initial_source_state_included':True,'calibrated_bootstrap_ordinal136_included':True}

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--source',type=Path,default=DEFAULT_SOURCE)
    p.add_argument('--certificate',type=Path,help='Verify a supplied certificate instead of deriving one.')
    p.add_argument('--output',type=Path,help='Write a derived or verified certificate to this path.')
    a=p.parse_args();raw=a.source.read_bytes();digest=hashlib.sha256(raw).hexdigest()
    if digest!=SOURCE_SHA256:raise ValueError('Unexpected baseline source digest')
    rows=json.loads(raw);graph=graph_intervals(rows)
    if a.certificate:
        old=json.loads(a.certificate.read_text())
        if old['source_sha256']!=digest:raise ValueError('Certificate source mismatch')
        domains=old['domains']
    else:domains=derive(rows,graph)
    receipt=verify(rows,graph,domains);report={'source_sha256':digest,'domains':domains,**receipt}
    output=a.output or (None if a.certificate else Path(__file__).with_name('source_zero_certificate.json'))
    if output:output.write_text(json.dumps(report,separators=(',',':'))+'\n')
    print(json.dumps(receipt,indent=2))

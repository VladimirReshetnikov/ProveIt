#!/usr/bin/env python3
"""Finite independent abstract interpretation of the published register tree.

Domain for each register: subsets of {0,1,...,K,>K}, with the last atom an
unbounded tail. Worklist joins yield an inductive overapproximation from the
actual nextproof=2 root. No runtime/oracle instruction is executed.
"""
from __future__ import annotations
import argparse, hashlib, json, re
from pathlib import Path
from collections import deque, Counter

def parse(path):
    raw=path.read_bytes();body=raw.decode().split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
    edge=r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    nodes=re.findall(r'\(('+edge+r'),\s*('+edge+r')\)',body)
    assert len(nodes)==6459
    sites=[];todo=[('CN 0','')]
    while todo:
        e,p=todo.pop();op,*r=e.split()
        if op=='CN':
            l,v=nodes[int(r[0])];todo.extend([(v,p+'1'),(l,p+'0')])
        else:sites.append((p,op,int(r[0]) if r else None))
    assert len(sites)==6460
    return raw,nodes,sites

def inc(p):
    at=p.rfind('0')
    return ('0'*len(p)) if at<0 else p[:at]+'1'+'0'*(len(p)-at-1)

def strip(bit,k,p):
    while k and p:
        k-=p[-1]==bit;p=p[:-1]
    return p

def cfg(nodes,sites):
    index={p:i for i,(p,_,_) in enumerate(sites)}
    def target(p):
        n=0;k=0;read=''
        while True:
            b=p[k] if k<len(p) else '0';read+=b;k+=1
            e=nodes[n][int(b)];op,*r=e.split()
            if op!='CN':return index[read]
            n=int(r[0]);assert k<=35
    edges=[]
    for p,op,r in sites:
        if op=='CI':e=[('inc',target(inc(p)),r)]
        elif op=='CD':e=[('zero',target(inc(strip('0',1,p))),r),('dec',target(inc(p)),r)]
        elif op=='CB':e=[('nop',target(inc(strip('0',r,p))),None)]
        elif op=='CC':e=[('nop',target(strip('1',r,p)),None)]
        else:e=[]
        edges.append(e)
    return target(''),edges

def transfer(mask,kind,K):
    # Atom K+1 denotes all values >=K+1.
    if kind=='zero':return mask&1
    if kind=='nop':return mask
    out=0
    for v in range(K+2):
        if (mask>>v)&1:
            if kind=='inc':out|=1<<min(K+1,v+1)
            elif kind=='dec' and v>0:
                out|=1<<(v-1)
                if v==K+1:out|=1<<(K+1)
    return out

def analyze(sites,edges,start,K,nextproof=2):
    at=[None for _ in sites];initial=[1]*9;initial[0]=1<<min(nextproof,K+1);at[start]=initial
    work=deque([start]);queued={start};updates=0
    while work:
        i=work.popleft();queued.remove(i);s=at[i]
        for kind,j,r in edges[i]:
            value=transfer(s[r],kind,K) if r is not None else 1
            if value==0:continue
            v=s.copy()
            if r is not None:v[r]=value
            old=at[j];joined=v if old is None else [x|y for x,y in zip(old,v)]
            if old!=joined:
                at[j]=joined;updates+=1
                if j not in queued:queued.add(j);work.append(j)
    return at,updates

def audit(sites,edges,start,K,at,nextproof=2):
    initial=[1]*9;initial[0]=1<<min(nextproof,K+1)
    assert all(v & ~at[start][r]==0 for r,v in enumerate(initial))
    obligations=0
    for i,s in enumerate(at):
        if s is None:continue
        for kind,j,r in edges[i]:
            value=transfer(s[r],kind,K) if r is not None else 1
            if not value:continue
            assert at[j] is not None
            for reg,mask in enumerate(s):
                v=value if reg==r else mask
                assert v&~at[j][reg]==0
            obligations+=1
    return obligations

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('program',type=Path)
    ap.add_argument('--cutoff',type=int,default=2);ap.add_argument('--output',type=Path,default=Path('register_abstract.json'))
    ap.add_argument('--nextproof',type=int,default=2)
    a=ap.parse_args();assert 0<=a.cutoff<=31 and a.nextproof>=0
    raw,nodes,sites=parse(a.program);start,edges=cfg(nodes,sites)
    at,updates=analyze(sites,edges,start,a.cutoff,a.nextproof);obligations=audit(sites,edges,start,a.cutoff,at,a.nextproof)
    forced=[]
    for i,(p,op,r) in enumerate(sites):
        if at[i] is not None and op=='CD':
            mask=at[i][r]
            if mask==1 or mask&1==0:forced.append({'site':i,'path':p,'register':r,'value_mask':mask,'branch':'zero' if mask==1 else 'positive'})
    impossible=[]
    for r in range(9):
        for s in range(r+1,9):
            witnesses=[]
            for i,(_,op,j) in enumerate(sites):
                if at[i] is not None and op in ('CI','CD') and j in (r,s):
                    other=s if j==r else r
                    if at[i][other]!=1:
                        witnesses.append({'site':i,'touched':j,'other_mask':at[i][other]})
                        if len(witnesses)==3:break
            impossible.append({'registers':[r,s],'coalescing_certified':not witnesses,'obstructions':witnesses})
    out={'program_sha256':hashlib.sha256(raw).hexdigest(),'initial_nextproof':a.nextproof,'cutoff':a.cutoff,'domain_atoms':list(range(a.cutoff+1))+['greater'],
         'sites':len(sites),'reachable_sites':sum(s is not None for s in at),'unreachable_sites':[i for i,s in enumerate(at) if s is None],
         'worklist_updates':updates,'checked_inductive_edges':obligations,'forced_decrements':forced,
         'branch_counts':dict(Counter(x['branch'] for x in forced)),'register_coalescing':impossible,
         'invariant':at,
         'scope':'Finite executable induction certificate for actual register semantics; not a binary-machine proof.'}
    a.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:out[k] for k in ('sites','reachable_sites','worklist_updates','checked_inductive_edges','branch_counts')},indent=2))
    print('Safe register pairs:',[x['registers'] for x in impossible if x['coalescing_certified']])
    print('Forced examples:',forced[:20])

if __name__=='__main__':main()

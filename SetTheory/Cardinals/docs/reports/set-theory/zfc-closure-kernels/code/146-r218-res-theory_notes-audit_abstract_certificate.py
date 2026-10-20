#!/usr/bin/env python3
"""Independent finite certificate checker for a seeded register-program invariant.

Abstract cells are the five natural-number sets {0},{1},{2},{3},{n>=4}.
A five-bit mask denotes a union; each source ordinal carries a product of
nine such unions, or None for the empty set of configurations. This checks
inductiveness directly, without trusting the fixed-point search that emitted
it. The CFG is resolved here from source paths without importing its resolver.
"""
import argparse,hashlib,json
from pathlib import Path

def need(p,m):
    if not p: raise ValueError(m)

def compile_cfg(rows):
    paths={p:i for i,(p,_,_) in enumerate(rows)}
    bounds={}
    def walk(p):
        if p in paths: ans=(paths[p],paths[p]+1)
        else:
            a,b=walk(p+'0'),walk(p+'1')
            need(a[1]==b[0],('noncontiguous',p))
            ans=(a[0],b[1])
        bounds[p]=ans
        return ans
    need(walk('')==(0,len(rows)),'bad root')
    def cut(p,kind,n):
        while p:
            c,p=p[-1],p[:-1]
            if c==kind:
                n-=1
                if n==0:return bounds[p][1]%len(rows) if kind=='0' else bounds[p][0]
        return 0
    cfg=[]
    for i,(p,op,a) in enumerate(rows):
        after=(i+1)%len(rows)
        if op=='CI': targets=[after]
        elif op=='CD':targets=[cut(p,'0',1),after]
        elif op=='CB':targets=[cut(p,'0',a)]
        elif op=='CC':targets=[cut(p,'1',a)]
        elif op=='CH':targets=[]
        else:raise ValueError(('bad opcode',op))
        cfg.append(targets)
    return cfg

def inc(mask):
    return ((mask&7)<<1)|(16 if mask&24 else 0)

def positive_dec(mask):
    return ((mask&14)>>1)|(24 if mask&16 else 0)

def check(rows,domains,initial):
    need(len(rows)==len(domains),'length mismatch')
    cfg=compile_cfg(rows)
    for d in domains:
        need(d is None or (len(d)==9 and all(type(m)is int and 0<m<32 for m in d)),'malformed abstract cell')
    need(domains[0]is not None,'empty entry')
    need(all(domains[0][i]&(1<<min(x,4))for i,x in enumerate(initial)),'initial state absent')
    checks=0
    for i,((path,op,r),dom,targets) in enumerate(zip(rows,domains,cfg)):
        if dom is None:continue
        successors=[]
        if op=='CI':
            dd=list(dom);dd[r]=inc(dd[r]);successors=[(targets[0],dd)]
        elif op=='CD':
            if dom[r]&1:
                dd=list(dom);dd[r]=1;successors.append((targets[0],dd))
            if dom[r]&30:
                dd=list(dom);dd[r]=positive_dec(dd[r]);successors.append((targets[1],dd))
        else:successors=[(j,dom)for j in targets]
        for j,dd in successors:
            need(domains[j]is not None,('reachable target marked empty',i,j))
            need(all(x&~y==0 for x,y in zip(dd,domains[j])),('closure violation',i,j,dd,domains[j]))
            checks+=1
    dead=[i for i,d in enumerate(domains)if d is None]
    zeros=[i for i,((_,op,r),d)in enumerate(zip(rows,domains))if op=='CD'and d is not None and d[r]==1]
    return {'status':'INDEPENDENT_INDUCTIVE_ABSTRACT_CERTIFICATE_PASS','closure_edges':checks,'unreachable_ordinals':dead,'always_zero_decrements':zeros,'initial_registers':initial,'semantics':'Product of unions of {0},{1},{2},{3},{n>=4}; checked closure covers all natural registers, with no execution bound.'}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('sites',type=Path);ap.add_argument('certificate',type=Path);ap.add_argument('output',type=Path);args=ap.parse_args()
    rows=json.loads(args.sites.read_bytes());cert=json.loads(args.certificate.read_bytes())
    r=check(rows,cert['domains'],[3,0,0,0,3,0,0,0,0])
    r['source_sha256']=hashlib.sha256(args.sites.read_bytes()).hexdigest();r['certificate_sha256']=hashlib.sha256(args.certificate.read_bytes()).hexdigest()
    args.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
if __name__=='__main__':main()

#!/usr/bin/env python3
"""Exact source-only certificate for guarded jump-to-decrement substitutions.
No TM compilation, blank startup, or PA kernel formalization is claimed.
All safety checks are explicit exceptions, including under Python -O.
"""
from pathlib import Path
import hashlib,json,re
from collections import deque
ROOT=Path(__file__).resolve().parent
SOURCE_SHA='8c7c6c6884ecbb8f56e893404bb81162db15ef3dd6fd3212881a93994d63d872'
def require(c,s):
    if not c:raise ValueError(s)
def parse_source():
    data=(ROOT/'Program.lean').read_bytes()
    require(hashlib.sha256(data).hexdigest()==SOURCE_SHA,'Unrecognized source bytes')
    nodes={}
    for line in data.decode().splitlines():
        m=re.match(r'def (\w+) : Tree := \.node (.*)',line)
        if not m:continue
        tokens=re.findall(r'\(\.leaf \(\.(\w+)(?: (\d+))?\)\)|\b((?:node|x)\d+)\b',m[2])
        ch=[nodes[name]if name else ('leaf',op,int(arg)if arg else None)for op,arg,name in tokens]
        require(len(ch)==2,'Tree parser arity mismatch')
        nodes[m[1]]=tuple(ch)
    sites=[]
    def flat(t,p):
        if len(t)==3 and t[0]=='leaf':sites.append((p,t[1],t[2]));return
        flat(t[0],p+(0,));flat(t[1],p+(1,))
    flat(nodes['node172'],())
    require(len(sites)==3812,'Site count changed')
    lookup={p:i for i,(p,_,_)in enumerate(sites)}
    def locate(p):
        if p in lookup:return lookup[p]
        for i,(q,_,_)in enumerate(sites):
            if q[:len(p)]==p or(p[:len(q)]==q and not any(p[len(q):])):return i
        return None
    def after(p):
        for i in range(len(p)-1,-1,-1):
            if p[i]==0:return locate(p[:i]+(1,))
        return 0
    def cut(p,b,k):
        for i in range(len(p)-1,-1,-1):
            if p[i]==b:
                k-=1
                if k==0:return p[:i]
        raise ValueError(('Bad control depth',p,b,k))
    code=[]
    for p,op,a in sites:
        if op=='inc':q=('inc',a,after(p))
        elif op=='dec':q=('dec',a,after(cut(p,0,1)),after(p))
        elif op=='breakTo':q=('jump',after(cut(p,0,a)))
        elif op=='continueTo':q=('jump',locate(cut(p,1,a)))
        elif op=='halt':q=('halt',)
        else:raise ValueError(op)
        require(all(x is not None for x in q),'Unresolved control target')
        code.append(q)
    return sites,code

def successors(op,mask):
    if op[0]=='inc':return ((op[2],mask|(1<<op[1])),)
    if op[0]=='jump':return ((op[1],mask),)
    if op[0]=='halt':return ()
    _,r,z,p=op
    if not mask>>r&1:return ((z,mask),)
    return ((p,mask),(p,mask&~(1<<r)))
def compute(code):
    seen={(25,1)};todo=deque(seen)
    while todo:
        pc,m=todo.popleft()
        for s in successors(code[pc],m):
            if s not in seen:seen.add(s);todo.append(s)
    masks=[set()for _ in code]
    for pc,m in seen:masks[pc].add(m)
    return masks

def verify_closure(code,masks):
    require(1 in masks[25],'Initial mask missing')
    for pc,ms in enumerate(masks):
        for m in ms:
            require(0<=m<512,'Invalid nine-register mask')
            for k,n in successors(code[pc],m):
                require(n in masks[k],f'Closure fails at {pc},{m} -> {k},{n}')
def replacement(code,sites,masks,targets):
    out=list(code)
    for pc,r in targets:
        require(sites[pc][1:]==('breakTo',1),'Replacement site is not CB1')
        require(masks[pc]and all(not(m>>r&1)for m in masks[pc]),'Register not proved zero')
        old=code[pc];out[pc]=('dec',r,old[1],pc+1)
        for m in masks[pc]:require(successors(out[pc],m)==successors(old,m),'Restricted transition changed')
    verify_closure(out,masks)
    return out

def main():
    sites,code=parse_source();masks=compute(code);verify_closure(code,masks)
    require(sum(map(len,masks))==274880,'Invariant pair census differs')
    zero=[]
    for ms in masks:
        pos=0
        for m in ms:pos|=m
        zero.append([r for r in range(9)if ms and not(pos>>r&1)])
    eligible=[{'site':pc,'path':''.join(map(str,p)),'registers':zero[pc]}for pc,(p,op,a)in enumerate(sites)if(op,a)==('breakTo',1)and zero[pc]]
    all6=[(x['site'],6)for x in eligible if 6 in x['registers']]
    a=replacement(code,sites,masks,[(26,6)]);b=replacement(code,sites,masks,all6)
    encoded=[format(sum(1<<m for m in ms),'x')for ms in masks]
    (ROOT/'joint_mask_certificate.json').write_text(json.dumps({'source_sha256':SOURCE_SHA,'initial':[25,1],'site_masks_hex':encoded},separators=(',',':'))+'\n')
    (ROOT/'zero_registers_by_site.json').write_text(json.dumps(zero,separators=(',',':'))+'\n')
    for name,ops in [('source26_cd6',a),('all_eligible_cd6',b)]:
        (ROOT/(name+'.json')).write_text(json.dumps([{'path':''.join(map(str,p)),'instruction':ops[pc]}for pc,(p,_,_)in enumerate(sites)],separators=(',',':'))+'\n')
    receipt={'status':'SOURCE_TRANSITION_IDENTITY_ON_INDUCTIVE_INVARIANT','source_sha256':SOURCE_SHA,'sites':len(code),'invariant_pairs':sum(map(len,masks)),'site26_masks':sorted(masks[26]),'site26_zero_registers':zero[26],'eligible_CB1_sites':eligible,'single_cd6_site':26,'joint_cd6_sites':[pc for pc,r in all6],'physical_binding':'Not provided by this source-only certificate'}
    (ROOT/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items()if k not in('eligible_CB1_sites','site26_masks')},indent=2))
if __name__=='__main__':main()

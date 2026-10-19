#!/usr/bin/env python3
"""A finite specialization diagnostic for the local move-to-front operation.

This is deliberately not a compiler: the mutant's header continuation is
incompatible with the old representation. See mtf-local.tex. Parsing and CFG
normalization follow the attributed Prefix246/reachable_guards development;
the permutation specialization and zero-name quotient are new here.
"""
from pathlib import Path
from hashlib import sha256
from collections import deque,Counter
import argparse,json,re,time

PIN='1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746'
INITIAL=(4,1,1,1,4,1,1,1,1)
ORDER=(2,8,1,4,3,7,0,5,6)

def parse(path):
    raw=path.read_bytes();assert sha256(raw).hexdigest()==PIN
    body=raw.decode('ascii').split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
    term=r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    pat=r'\(('+term+r'),\s*('+term+r')\)';rows=re.findall(pat,body)
    assert len(rows)==6459 and not re.sub(r'[\s;]','',re.sub(pat,'',body))
    sites=[];seen=set()
    def visit(n,p,active):
        assert n not in active and 0<=n<len(rows);seen.add(n)
        for bit,text in enumerate(rows[n]):
            op,*args=text.split();r=int(args[0]) if args else None;pc=p+str(bit)
            if op=='CN':visit(r,pc,active|{n})
            else:sites.append((pc,op,r))
    visit(0,'',set());assert len(sites)==6460 and len(seen)==6459
    bypc={pc:i for i,(pc,op,r) in enumerate(sites)}
    def decode(pc):
        word=pc+'0'*40
        for k in range(len(word)+1):
            if word[:k] in bypc:
                assert all(x=='0' for x in word[k:]);return bypc[word[:k]]
        raise AssertionError(pc)
    def inc(pc):return '' if '0' not in pc else pc[:pc.rindex('0')]+'1'
    def strip(pc,bit,count):
        while pc and count:count-=pc[-1]==bit;pc=pc[:-1]
        return pc
    edges={}
    for i,(pc,op,r) in enumerate(sites):
        for zero in ((True,False) if op=='CD' else (None,)):
            if op=='CI' or op=='CD' and not zero:p=inc(pc)
            elif op=='CD':p=inc(strip(pc,'0',1))
            elif op=='CB':p=inc(strip(pc,'0',r))
            elif op=='CC':p=strip(pc,'1',r)
            else:edges[i,zero]=None;continue
            edges[i,zero]=decode(p)
    return sites,edges,decode('')

def advance(v,op,r,zero):
    if op=='CD' and not(v[r]&(1 if zero else 6)):return None
    out=list(v)
    if op=='CI':out[r]=(2 if v[r]&1 else 0)|(4 if v[r]&6 else 0)
    if op=='CD':out[r]=1 if zero else ((1 if v[r]&2 else 0)|(6 if v[r]&4 else 0))
    return tuple(out)

def product(sites,edges,root):
    masks=[None]*len(sites);masks[root]=INITIAL;q=deque([root]);queued={root}
    while q:
        i=q.popleft();queued.remove(i);pc,op,r=sites[i]
        for zero in ((True,False) if op=='CD' else(None,)):
            v=advance(masks[i],op,r,zero);j=edges[i,zero]
            if v is None or j is None:continue
            joined=v if masks[j] is None else tuple(x|y for x,y in zip(masks[j],v))
            if joined!=masks[j]:
                masks[j]=joined
                if j not in queued:queued.add(j);q.append(j)
    assert all(x&y==x for x,y in zip(INITIAL,masks[root]))
    for i,mask in enumerate(masks):
        if mask is None:continue
        pc,op,r=sites[i]
        for zero in ((True,False) if op=='CD' else(None,)):
            v=advance(mask,op,r,zero);j=edges[i,zero]
            if v is None or j is None:continue
            assert masks[j] is not None and all(x&y==x for x,y in zip(v,masks[j]))
    return masks

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--program',type=Path,required=True)
    ap.add_argument('--output',type=Path,default=Path(__file__).with_name('mtf-permutation-cfg.json'))
    args=ap.parse_args();sites,edges,root=parse(args.program);masks=product(sites,edges,root)
    def canon(i,p):
        assert masks[i] is not None
        zs=iter(sorted(r for r in p if masks[i][r]==1));out=list(p)
        for k,r in enumerate(p):
            if masks[i][r]==1:out[k]=next(zs)
        return tuple(out)
    initial=canon(root,ORDER);seen=[set() for i in sites];seen[root].add(initial)
    q=deque([(root,initial)]);selectors=[set() for i in sites];edge_count=0;began=time.monotonic()
    while q:
        i,p=q.popleft();pc,op,r=sites[i]
        if op in ('CI','CD'):selectors[i].add(p.index(r))
        for zero in ((True,False) if op=='CD' else(None,)):
            if advance(masks[i],op,r,zero) is None:continue
            j=edges[i,zero]
            if j is None:continue
            np=p
            if op=='CD' and zero:
                k=p.index(r);np=(r,)+p[:k]+p[k+1:]
            np=canon(j,np);edge_count+=1
            if np not in seen[j]:seen[j].add(np);q.append((j,np))
    # Independent closure pass over the completed finite relation.
    for i,ps in enumerate(seen):
        pc,op,r=sites[i]
        for p in ps:
            for zero in ((True,False) if op=='CD' else(None,)):
                if advance(masks[i],op,r,zero) is None:continue
                j=edges[i,zero]
                if j is None:continue
                k=p.index(r) if op=='CD' and zero else None
                np=(r,)+p[:k]+p[k+1:] if k is not None else p
                assert canon(j,np) in seen[j]
    counts=Counter(len(p) for p in seen);scounts=Counter(len(p) for p in selectors if p)
    out=dict(status='COMPLETE',program_sha256=PIN,site_permutation_pairs=sum(map(len,seen)),remaining=0,
        edges=edge_count,seconds=time.monotonic()-began,initial_value_masks=INITIAL,
        initial_physical_logical_names=ORDER,root_site=root,
        permutations_at_site_distribution=dict(sorted(counts.items())),
        physical_selector_choices=dict(sorted(scounts.items())),
        nonconstant_selector_example=next(([sites[i],sorted(p)] for i,p in enumerate(selectors) if len(p)>1),None),
        independent_closure_pass=True,
        assumptions=['Prepared source root, not a blank bootstrap for the mutant.',
            'Three-class product invariant overapproximates logical source executions.',
            'Each zero decrement moves its logical register name to the front.',
            'Names of registers proved zero at a site are sorted without moving their equal tape values.'],
        scope='Finite source CFG diagnostic only; the header continuation is unresolved. No compiler or consistency machine emitted.')
    assert out['site_permutation_pairs']==11117 and edge_count==14693
    args.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

if __name__=='__main__':main()

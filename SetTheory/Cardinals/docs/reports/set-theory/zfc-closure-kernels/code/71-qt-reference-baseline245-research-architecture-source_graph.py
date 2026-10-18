# Adapted from zfc-beyond246/alternative/verify_invariant.py; pinned prior-art input.
#!/usr/bin/env python3
"""Reparse the pinned source and check the prior natural-category invariant.

No worklist, imported generator or prior classification result is trusted.
The source decoder is reparsed. Every feasible abstract edge is checked.
"""
from pathlib import Path
import argparse,hashlib,json,re,time,zlib
HERE=Path(__file__).resolve().parent
PIN='1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746'
EXCLUDED=[8202,8203,8204,8358,8359,8360]

def source_graph():
    raw=(HERE/'reference/Prog254.v').read_bytes()
    assert hashlib.sha256(raw).hexdigest()==PIN
    body=raw.decode('ascii').split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
    term=r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    row=r'\(('+term+r'),\s*('+term+r')\)'
    tree=re.findall(row,body)
    assert len(tree)==6459
    assert not re.sub(r'[;\s]','',re.sub(row,'',body))
    def read(s):
        a=s.split();return a[0],int(a[1]) if len(a)>1 else None
    tree=[tuple(read(e) for e in x) for x in tree]
    sites=[];seen=set()
    def visit(node,path):
        assert node not in seen;seen.add(node)
        for bit,(op,arg) in enumerate(tree[node]):
            word=path+str(bit)
            if op=='CN':visit(arg,word)
            else:sites.append((word,op,arg))
    visit(0,'')
    assert seen==set(range(6459)) and len(sites)==6460
    bypath={s[0]:i for i,s in enumerate(sites)}
    def decode(word):
        node=0;path=''
        for _ in range(35):
            b=word[len(path)] if len(path)<len(word) else '0'
            path+=b;op,arg=tree[node][int(b)]
            if op=='CN':node=arg;continue
            assert '1' not in word[len(path):]
            return bypath[path]
        raise AssertionError('depth bound')
    def carry(word):
        bits=list(word);i=len(bits)-1
        while i>=0 and bits[i]=='1':bits[i]='0';i-=1
        if i>=0:bits[i]='1'
        return ''.join(bits)
    def drop(word,bit,n):
        i=len(word)
        while i and n:i-=1;n-=word[i]==bit
        return word[:i]
    cases=[]
    for site,(pc,op,arg) in enumerate(sites):
        for zero in ((True,False) if op=='CD' else (None,)):
            if op=='CI' or (op=='CD' and not zero):nextword=carry(pc)
            elif op=='CD':nextword=carry(drop(pc,'0',1))
            elif op=='CB':nextword=carry(drop(pc,'0',arg))
            elif op=='CC':nextword=drop(pc,'1',arg)
            else:assert op=='CH';nextword=None
            cases.append((site,pc,op,arg,zero,None if nextword is None else decode(nextword)))
    assert len(cases)==8391 and decode('')==0
    return sites,cases

def possibilities(mask):
    assert mask in range(1,8)
    return [i for i in range(3) if mask&(1<<i)]

def image(mask,op,zero):
    result=set()
    for x in possibilities(mask):
        if op=='CI':result.add(min(x+1,2))
        elif zero:
            if x==0:result.add(0)
        elif x==1:result.add(0)
        elif x==2:result.update((1,2))
    return sum(1<<i for i in result)

def check_product(cases):
    data=json.loads((HERE/'reference/product-invariant.json').read_text())
    assert data['program_sha256']==PIN
    assert data['logical_register_order']==['N','T','W','A','D','H','X','Y','L']
    initial=[7,1,1,7,7,1,7,7,7]
    assert data['initial_masks']==initial
    v=data['masks'];assert len(v)==6460
    for row in v:
        if row is not None:assert len(row)==9 and all(x in range(1,8) for x in row)
    assert all(a&~b==0 for a,b in zip(initial,v[0]))
    rejected=[];edges=0
    for index,(i,pc,op,arg,zero,j) in enumerate(cases):
        w=None if v[i] is None else list(v[i])
        if w is not None and op in ('CI','CD'):
            w[arg]=image(w[arg],op,zero)
            if not w[arg]:w=None
        if w is None:rejected.append(index);continue
        if j is not None:
            assert v[j] is not None
            assert all(a&~b==0 for a,b in zip(w,v[j])),(index,i,j)
            edges+=1
    assert rejected==EXCLUDED==data['excluded_case_indices']
    return dict(status='PASS',scope='Every N,A,D,X,Y,L; T=W=H=0 at root.',
        reachable_sites=sum(x is not None for x in v),feasible_guards=8391-len(rejected),
        feasible_nonhalting_edges=edges,excluded_case_indices=rejected,
        excluded_cases=[list(cases[i][1:5]) for i in rejected])

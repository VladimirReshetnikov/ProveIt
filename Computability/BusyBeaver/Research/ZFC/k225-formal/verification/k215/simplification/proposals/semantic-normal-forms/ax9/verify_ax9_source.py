#!/usr/bin/env python3
"""Rebuild AX9 source edits and check their finite graph/prefix evidence.

This does NOT prove a complete binary-table implementation or a new state
count. The arithmetic experiments are finite corroboration of the written
all-natural macro argument. No optimizer or external executable is invoked.
"""
from __future__ import annotations
import argparse
import hashlib
import itertools
import json
from pathlib import Path

BASE_SHA = '17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'
DROP_PATH = '11010010010000'

def require(b, why):
    if not b:
        raise ValueError(why)

def is_leaf(t):
    return isinstance(t[0], str)

def parse(rows):
    root = {}
    for path, op, arg in rows:
        at = root
        for bit in path:
            require(bit in '01' and 'leaf' not in at, 'bad path')
            at = at.setdefault(bit, {})
        require(not at, 'overlapping/duplicate path')
        at['leaf'] = (op,arg)
    def go(at):
        if 'leaf' in at:
            require(set(at)=={'leaf'}, 'leaf with children')
            return at['leaf']
        require(set(at)=={'0','1'}, 'nonfull tree')
        return go(at['0']),go(at['1'])
    t=go(root)
    require(flatten(t)==rows, 'noncanonical leaf order')
    return t

def flatten(t,path=''):
    if is_leaf(t):
        return [[path,*t]]
    return flatten(t[0],path+'0')+flatten(t[1],path+'1')

def at(t,path):
    for b in path:
        t=t[int(b)]
    return t

def replace(t,path,new):
    if not path:
        return new
    b=int(path[0]);v=list(t);v[b]=replace(v[b],path[1:],new)
    return tuple(v)

def metrics(t):
    seen=set()
    def go(n):
        if n in seen:
            return
        seen.add(n)
        if not is_leaf(n):
            go(n[0]);go(n[1])
    go(t);rows=flatten(t)
    return dict(dag_nodes=len(seen),leaves=len(rows),
                max_depth=max(len(p) for p,_,_ in rows),
                max_zero_run=max(len(x) for p,_,_ in rows for x in p.split('1')))

def graph(rows):
    leaves={p:i for i,(p,_,_) in enumerate(rows)};spans={}
    def go(path):
        if path in leaves:
            ans=(leaves[path],leaves[path]+1)
        else:
            a,b=go(path+'0'),go(path+'1')
            require(a[1]==b[0], 'nonadjacent spans')
            ans=(a[0],b[1])
        spans[path]=ans
        return ans
    go('')
    def cut(path,bit,k):
        while path:
            b=path[-1];path=path[:-1]
            if b==bit:
                k-=1
                if not k:
                    return (spans[path][1] if bit=='0' else spans[path][0]) % len(rows)
        return 0
    answer=[]
    for i,(path,op,arg) in enumerate(rows):
        nxt=(i+1)%len(rows)
        if op=='CI':
            answer.append((op,arg,(nxt,)))
        elif op=='CD':
            answer.append((op,arg,(cut(path,'0',1),nxt)))
        elif op in ('CB','CC'):
            answer.append((op,arg,(cut(path,'0' if op=='CB' else '1',arg),)))
        elif op=='CH':
            answer.append((op,arg,()))
        else:
            raise ValueError('unknown opcode')
    return answer

def run_fragment(g,start,end,regs,limit=1000000):
    r=list(regs);pc=start;steps=0
    while pc!=end:
        require(steps<limit, 'finite experiment exceeded explicit cap')
        op,arg,succ=g[pc]
        if op=='CI':
            r[arg]+=1;pc=succ[0]
        elif op=='CD':
            if r[arg]:
                r[arg]-=1;pc=succ[1]
            else:
                pc=succ[0]
        elif op in ('CB','CC'):
            pc=succ[0]
        else:
            raise ValueError('unexpected halt in arithmetic prefix')
        steps+=1
    return r,steps

def pairing(a,b):
    return (a+b)*(a+b+1)//2+b

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--base',type=Path,default=Path(__file__).with_name('reference')/'sites215.json')
    ap.add_argument('--out',type=Path)
    a=ap.parse_args()
    raw=a.base.read_bytes()
    require(hashlib.sha256(raw).hexdigest()==BASE_SHA, 'wrong pinned parent bytes')
    rows=json.loads(raw);t=parse(rows)
    require([i for i,r in enumerate(rows) if r[0].startswith(DROP_PATH)]==list(range(26,45)), 'wrong closed block')
    small=replace(t,DROP_PATH,(('CD',1),('CC',1)))
    biased=replace(t,DROP_PATH[:-1],at(t,DROP_PATH[:-1]+'1'))
    newrows=flatten(biased);go,gn=graph(rows),graph(newrows)
    def image(i):
        require(not (27<=i<45), 'outside edge enters internal removed instruction')
        if i==26:
            return 26
        return i if i<26 else i-19
    checked=0
    for i,(op,arg,succ) in enumerate(go):
        if 26<=i<45:
            continue
        j=i if i<26 else i-19
        require(gn[j]==(op,arg,tuple(image(k) for k in succ)), 'surviving CFG edge changed')
        checked+=len(succ)
    max_steps=0;cases=0
    for tv,w,d,h in itertools.product(range(4),repeat=4):
        regs=[3,tv,w,5,d,h,0,0,7]
        old,so=run_fragment(go,26,107,regs)
        new,sn=run_fragment(gn,26,88,regs)
        eo=list(regs);eo[1]=4*pairing(d,h)+2;eo[2]=pairing(tv,w)
        en=list(regs);en[1]=4*pairing(tv+d,h)+2
        require(old==eo and new==en, 'prefix arithmetic corroboration failed')
        max_steps=max(max_steps,so,sn);cases+=1
    data={
        'status':'PASS_FINITE_GRAPH_AND_ARITHMETIC_CHECKS',
        'pin':'b07002a86bcc96e76a31b57dce23d3b8c2b76fa6',
        'parent_sha256':BASE_SHA,
        'parent':metrics(t),'clear_ax9':metrics(small),'top_biased_ax9':metrics(biased),
        'surviving_edges_checked':checked,'finite_arithmetic_cases':cases,
        'arithmetic_domain':'top, raw stack, counter, cache independently in {0,1,2,3}; N=3,C=5,L=7; scratches zero',
        'maximum_fragment_steps':max_steps,
        'source_only':True,'binary_table_claim':False,
        'scope':'The finite arithmetic cases corroborate the written unbounded macro argument; they are not its proof.'
    }
    sources={'ax9-clear.sites.json':flatten(small),'ax9-biased.sites.json':newrows}
    data['derived_source_sha256']={name:hashlib.sha256((json.dumps(v,separators=(',',':'))+'\n').encode()).hexdigest() for name,v in sources.items()}
    if a.out:
        a.out.mkdir(parents=True,exist_ok=False)
        for name,v in sources.items():
            (a.out/name).write_text(json.dumps(v,separators=(',',':'))+'\n')
        (a.out/'source_check.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(data,indent=2))

if __name__=='__main__':
    main()

#!/usr/bin/env python3
"""Exact finite source-graph check; no physical TM correctness is asserted.

Parses the pinned Lean tree definitions and the separate-head grammar, resolves
all primitive instructions, and verifies source-preserving root/MP rotations.
"""
from pathlib import Path
import json,re,hashlib
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent

def load_nodes():
    nodes={}
    for line in (ROOT/'inputs/Program.lean').read_text().splitlines():
        m=re.match(r'def (\w+) : Tree := \.node (.*)',line)
        if not m:continue
        tokens=re.findall(r'\(\.leaf \(\.(\w+)(?: (\d+))?\)\)|\b((?:node|x)\d+)\b',m[2])
        out=[name if name else ('leaf',op,int(arg) if arg else None)for op,arg,name in tokens]
        assert len(out)==2
        nodes[m[1]]=tuple(out)
    return nodes

def grammar():
    g=json.loads((ROOT/'inputs/pa194.grammar.json').read_text())
    def expand(x):
        if isinstance(x,list):return tuple(x)
        if x in g['rules']:return tuple(expand(y)for y in g['rules'][x])
        return x
    return expand(g['root'])

def resolve(nodes):
    sites=[];ax=grammar()
    def walk(t,path=(),inside=False):
        if isinstance(t,str):
            if t=='x67':return walk(ax,path,True)
            return walk(nodes[t],path,inside)
        if t[0]=='leaf':sites.append((path,t[1],t[2],inside));return
        walk(t[0],path+(0,),inside);walk(t[1],path+(1,),inside)
    walk('node172')
    bypath={p:i for i,(p,_,_,_)in enumerate(sites)}
    def enter(p):
        if p in bypath:return bypath[p]
        for i,(q,_,_,_)in enumerate(sites):
            if q[:len(p)]==p or (p[:len(q)]==q and not any(p[len(q):])):return i
        raise AssertionError(('invalid tree entry',p))
    def after(p):
        for i in range(len(p)-1,-1,-1):
            if p[i]==0:return enter(p[:i]+(1,))
        raise AssertionError(('outside root',p))
    def enclosing(p,bit,count):
        assert count>0
        for i in range(len(p)-1,-1,-1):
            if p[i]==bit:
                count-=1
                if not count:return p[:i]
        raise AssertionError(('invalid jump depth',p,bit,count))
    instructions=[]
    for p,op,r,_ in sites:
        if op=='inc':line=['inc',r,after(p)]
        elif op=='dec':line=['dec',r,after(enclosing(p,0,1)),after(p)]
        elif op=='breakTo':line=['jump',after(enclosing(p,0,r))]
        elif op=='continueTo':line=['jump',enter(enclosing(p,1,r))]
        elif op=='halt':line=['halt']
        else:raise AssertionError(op)
        instructions.append(line)
    return sites,instructions

def verify():
    nodes=load_nodes();before,old=resolve(nodes)
    pinned=json.loads((ROOT/'inputs/pa194.instructions.json').read_text())
    assert old==pinned and len(old)==3673
    nodes.update(node21=('node20','node170'),node171=('node21','node23'),node172=('node7','node171'),node162=('node37','node163'),node164=('node75','node162'))
    after,new=resolve(nodes)
    assert old==new and len(after)==3673
    assert [(op,r)for p,op,r,inside in before]==[(op,r)for p,op,r,inside in after]
    maxzero=lambda p:max(map(len,re.findall('0+',''.join(map(str,p)))),default=0)
    fixed=[(i,p,op,r)for i,(p,op,r,inside)in enumerate(after)if not inside]
    assert ''.join(map(str,before[0][0]))=='000000'
    assert ''.join(map(str,after[0][0]))=='00000'
    assert all(maxzero(p)<=5 for i,p,op,r in fixed)
    assert all(maxzero(p)<=4 for i,p,op,r in fixed if op=='inc')
    # Literal two-cell observation explaining the physical history issue.
    raw=(ROOT/'verification/helper_obstruction/primary201.native.tm').read_text()
    rows={}
    for line in raw.splitlines():
        q,b,w,d,n=line.split();rows[int(q),int(b)]=(int(w),1 if d=='R'else -1,int(n))
    targets=[]
    for history in (0,1):
        tape={-1:history,0:0};q=69;pos=0
        for _ in range(3):
            assert pos in tape
            w,d,q=rows[q,tape[pos]];tape[pos]=w;pos+=d
        assert pos==1 and tape=={-1:history,0:0}
        targets.append(q)
    assert targets==[104,105]
    return {'status':'PASS_SOURCE_ONLY','source_sites':3673,'all_resolved_instructions_identical':True,'first_path_before':'000000','first_path_after':'00000','fixed_sites':len(fixed),'max_fixed_zero_run':max(maxzero(p)for i,p,op,r in fixed),'max_fixed_increment_zero_run':max(maxzero(p)for i,p,op,r in fixed if op=='inc'),'native69_history_targets':targets,'physical_193_machine_certified':False}

if __name__=='__main__':
    if not __debug__:raise RuntimeError('Do not use Python -O.')
    print(json.dumps(verify(),indent=2))

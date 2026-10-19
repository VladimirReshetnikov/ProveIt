#!/usr/bin/env python3
"""Recheck all 15 AX helpers by test-to-test source bisimulation.

Each side is a closed macro followed by halt. Between decrement tests, only
register increments and control moves occur. Equal increment multiplicities
and equal tested registers justify the finite branch-closed relation for all
natural register vectors. This is source evidence, not a binary-TM theorem.
"""
from pathlib import Path
from collections import Counter
from functools import lru_cache
import json
import source_model as model
HERE=Path(__file__).resolve().parent
old={int(i):tuple(map(tuple,p)) for i,p in json.loads((model.DATA_DIR/'original219.json').read_text())['nodes'].items()}

def inc(path):
    return format((int(path,2)+1)%(1<<len(path)),f'0{len(path)}b') if path else ''
def strip(path,bit,k):
    at=len(path)
    while k and at:
        at-=1
        if path[at]==bit:k-=1
    return path[:at]
class Program:
    def __init__(self,nodes,root):self.nodes,self.root=nodes,root
    def leaf(self,path):
        e=('N',self.root);q='';i=0
        for _ in range(len(self.nodes)+2):
            if e[0]!='N':return e,q
            b=path[i] if i<len(path) else '0';q+=b;i+=1;e=self.nodes[e[1]][int(b)]
        raise AssertionError('cyclic source')
    def segment(self,path):
        c=Counter()
        for _ in range(1000):
            e,q=self.leaf(path)
            if e[0]=='I':c[e[1]]+=1;path=inc(q)
            elif e[0]=='B':path=inc(strip(q,'0',e[1]))
            elif e[0]=='C':path=strip(q,'1',e[1])
            else:return tuple(sorted(c.items())),path
        raise AssertionError('segment fuel exhaustion')

def oldmacro(m):
    nn=old.copy();root=max(nn)+1;nn[root]=('N',m),('H',);return Program(nn,root)
def newmacro(word):
    nn={};intern={}
    def pair(l,r):
        k=l,r
        if k not in intern:intern[k]=len(nn);nn[len(nn)]=k
        return ('N',intern[k])
    def seq(w):
        e=w[-1]
        for l in reversed(w[:-1]):e=pair(l,e)
        return e
    @lru_cache(None)
    def emit(t):
        if t[0]=='S':return seq([emit(x) for x in t[1:]])
        if t[0]=='A':return pair(emit(t[1]),emit(t[2]))
        return t
    root=pair(seq([emit(t) for t in word]),('H',))[1]
    return Program(nn,root)

def certificate(left,right):
    seen={};todo=[];rows=[]
    def add(a,b):
        ca,pa=left.segment(a);cb,pb=right.segment(b);assert ca==cb
        pair=pa,pb
        if pair not in seen:seen[pair]=len(rows);rows.append([pa,pb,None,None]);todo.append(pair)
        return seen[pair]
    add('','')
    while todo:
        pa,pb=todo.pop();ea,qa=left.leaf(pa);eb,qb=right.leaf(pb)
        assert ea==eb and ea[0] in ('D','H')
        i=seen[pa,pb]
        if ea[0]=='H':rows[i][2]=rows[i][3]=None
        else:
            rows[i][2]=add(inc(qa),inc(qb))
            rows[i][3]=add(inc(strip(qa,'0',1)),inc(strip(qb,'0',1)))
    # Independent closure replay of emitted finite relation.
    for i,(pa,pb,j,k) in enumerate(rows):
        ea,qa=left.leaf(pa);eb,qb=right.leaf(pb);assert ea==eb
        if ea[0]=='H':assert j is None and k is None;continue
        for sa,sb,target in ((inc(qa),inc(qb),j),(inc(strip(qa,'0',1)),inc(strip(qb,'0',1)),k)):
            ca,ra=left.segment(sa);cb,rb=right.segment(sb);assert ca==cb and rows[target][:2]==[ra,rb]
    return rows

def main():
    outputs=[]
    for macro,word in sorted(model.MACROS.items()):
        rows=certificate(oldmacro(macro),newmacro(word))
        outputs.append(dict(macro219=macro,test_pairs=len(rows),certificate=rows))
    result=dict(status='PASS',macros=len(outputs),total_related_pairs=sum(o['test_pairs'] for o in outputs),scope='All-natural-register closed helper bisimulations with an explicit halt continuation; no binary table.',helpers=outputs)
    (HERE/'macro_bridge.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='helpers'},indent=2))
if __name__=='__main__':main()

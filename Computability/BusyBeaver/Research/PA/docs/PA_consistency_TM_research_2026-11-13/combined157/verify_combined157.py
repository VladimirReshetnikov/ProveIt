#!/usr/bin/env python3
"""Check a 157-internal-node representation of the combined 197-state source.

This checks source control-flow equality only. It neither supplies a smaller
binary table nor proves a PA consistency biconditional.
"""
from pathlib import Path
import hashlib,json

HERE=Path(__file__).resolve().parent
BASE='combined197.tree.json'
NEW='combined157.tree.json'
OPS={'inc','dec','continueTo','breakTo','halt'}
def need(ok,msg):
    if not ok:raise ValueError(msg)
def freeze(t):
    need(isinstance(t,list)and len(t)==2,'malformed tree')
    if isinstance(t[0],str):
        need(t[0]in OPS and type(t[1])is int and t[1]>=0,'malformed leaf')
        return tuple(t)
    return freeze(t[0]),freeze(t[1])
def leaf(t):return isinstance(t[0],str)
def leaves(t,p=''):
    if leaf(t):return [(p,t)]
    return leaves(t[0],p+'0')+leaves(t[1],p+'1')
def count(t):
    seen=set();queue=[t]
    while queue:
        n=queue.pop()
        if n in seen:continue
        seen.add(n)
        if not leaf(n):queue.extend(n)
    return sum(not leaf(n)for n in seen)
def arithmetic(rows):
    indices={p:i for i,(p,o)in enumerate(rows)};depth=max(map(len,indices))
    def locate(prefix):
        w=prefix+'0'*depth
        for k in range(1,len(w)+1):
            if w[:k]in indices:
                need('1'not in prefix[k:],'stray nonzero path suffix')
                return indices[w[:k]]
        raise ValueError('unresolved successor')
    def inc(p):
        return format((int(p,2)+1)%(1<<len(p)),'0'+str(len(p))+'b') if p else ''
    def cut(p,b,n):
        at=[i for i,x in enumerate(p)if x==b];need(len(at)>=n,'insufficient ancestor depth')
        return p[:at[-n]]
    out=[]
    for p,(o,a)in rows:
        if o=='inc':out.append((o,a,locate(inc(p))))
        elif o=='dec':out.append((o,a,locate(inc(cut(p,'0',1))),locate(inc(p))))
        elif o=='breakTo':out.append(('jump',locate(inc(cut(p,'0',a)))))
        elif o=='continueTo':out.append(('jump',locate(cut(p,'1',a))))
        else:out.append(('halt',))
    return out
def intervals(t,rows):
    spans={};index=0
    def walk(n,p):
        nonlocal index
        start=index
        if leaf(n):index+=1
        else:walk(n[0],p+'0');walk(n[1],p+'1')
        spans[p]=(start,index)
    walk(t,'')
    def target(p,b,n):
        while p:
            last,p=p[-1],p[:-1]
            if last==b:
                n-=1
                if not n:return spans[p][1]%len(rows) if b=='0' else spans[p][0]
        raise ValueError('insufficient ancestor depth')
    out=[]
    for i,(p,(o,a))in enumerate(rows):
        after=(i+1)%len(rows)
        if o=='inc':out.append((o,a,after))
        elif o=='dec':out.append((o,a,target(p,'0',1),after))
        elif o=='breakTo':out.append(('jump',target(p,'0',a)))
        elif o=='continueTo':out.append(('jump',target(p,'1',a)))
        else:out.append(('halt',))
    return out
def main():
    result={};graphs=[];words=[]
    for name,expected in [(BASE,159),(NEW,157)]:
        data=(HERE/name).read_bytes();t=freeze(json.loads(data));rows=leaves(t)
        need(len(rows)==3573 and count(t)==expected,'unexpected source census')
        a,b=arithmetic(rows),intervals(t,rows);need(a==b,'independent CFG resolvers disagree')
        result[name]={'sha256':hashlib.sha256(data).hexdigest(),'source_sites':len(rows),
            'internal_nodes':count(t),'maximum_path_length':max(len(p)for p,o in rows),
            'maximum_zero_run':max(len(x)for p,o in rows for x in p.split('1')),
            'seed_path':rows[25][0]}
        graphs.append(a);words.append([o for p,o in rows])
    need(words[0]==words[1],'ordered primitive instruction word differs')
    need(graphs[0]==graphs[1],'source control flow differs')
    result['all_3573_ordered_primitive_instructions_equal']=True
    result['all_3573_source_rows_equal']=True
    result['scope']='Source representation only; no smaller binary machine or PA theorem.'
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()

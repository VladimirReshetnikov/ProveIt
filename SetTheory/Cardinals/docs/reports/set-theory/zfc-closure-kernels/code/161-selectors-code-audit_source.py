#!/usr/bin/env python3
"""Independent finite all-natural source bisimulation audit.
No imported source/compiler/runtime research modules; Python standard library.
The finite checks establish equality of primitive guarded transition graphs,
not the separate binary-machine runtime or initialization obligations.
"""
from pathlib import Path
import argparse, hashlib, json

def digest(raw): return hashlib.sha256(raw).hexdigest()
def canonical(x): return (json.dumps(x,separators=(',',':'))+'\n').encode()
def check(ok,msg):
    if not ok: raise ValueError(msg)

def build(rows):
    check(type(rows) is list and rows,'empty source')
    trie={}
    for i,row in enumerate(rows):
        check(type(row)is list and len(row)==3,'bad row')
        p,op,arg=row
        check(type(p)is str and p and set(p)<=set('01'),'bad path')
        check(op in ('CI','CD','CB','CC','CH'),'bad operation')
        if op=='CH':check(arg is None,'bad halt operand')
        elif op in ('CI','CD'):check(type(arg)is int and 0<=arg<9,'bad register')
        else:check(type(arg)is int and arg>0,'bad control depth')
        t=trie
        for b in p:
            check('row'not in t,'prefix conflict')
            t=t.setdefault(b,{})
        check(not t,'duplicate or prefix conflict')
        t['row']=i
    order=[];nodes=set()
    def walk(t):
        if 'row'in t:
            check(len(t)==1,'leaf children')
            i=t['row'];order.append(i)
            q=tuple(rows[i][1:]);nodes.add(q)
            return (i,i+1,q)
        check(set(t)=={'0','1'},'nonfull binary source')
        a,b=walk(t['0']),walk(t['1'])
        check(a[1]==b[0],'ordinal order')
        q=(a[2],b[2]);nodes.add(q)
        return (a[0],b[1],q)
    lo,hi,q=walk(trie)
    check(order==list(range(len(rows))) and lo==0 and hi==len(rows),'ordinal census')
    return trie,len(nodes)

def scoped_graph(rows,trie):
    """Interpret each pair as scoped break/continue targets, not bit arithmetic."""
    n=len(rows);graph=[None]*n
    def size(t):
        return 1 if 'row'in t else size(t['0'])+size(t['1'])
    def go(t,lo,breaks,continues):
        if 'row'in t:
            i=t['row'];p,op,r=rows[i];nxt=(i+1)%n
            target=lambda ss,k:ss[k-1] if k<=len(ss) else 0
            if op=='CI':ends=[nxt]
            elif op=='CD':ends=[target(breaks,1),nxt]
            elif op=='CB':ends=[target(breaks,r)]
            elif op=='CC':ends=[target(continues,r)]
            else:ends=[]
            graph[i]=[op,r,ends];return
        left=size(t['0']);total=left+size(t['1'])
        go(t['0'],lo,[(lo+total)%n]+breaks,continues)
        go(t['1'],lo+left,breaks,[lo]+continues)
    go(trie,0,[],[])
    return graph

def counter_graph(rows):
    """Independent bit-counter semantics, checking every dispatched suffix."""
    index={p:i for i,(p,_,_)in enumerate(rows)}
    depth=max(map(len,index))
    checks=0
    def dispatch(p):
        nonlocal checks
        checks+=1;word=p+'0'*(depth+1)
        for k in range(1,len(word)+1):
            if word[:k]in index:
                check('1'not in p[k:],'stray nonzero suffix')
                return index[word[:k]]
        raise ValueError('no dispatch')
    def inc(p):
        if not p:return ''
        b=list(p);carry=True
        for j in range(len(b)-1,-1,-1):
            if not carry:break
            if b[j]=='0':b[j]='1';carry=False
            else:b[j]='0'
        return ''.join(b)
    def leave(p,bit,k):
        for j in range(len(p)-1,-1,-1):
            if p[j]==bit:
                k-=1
                if k==0:return p[:j]
        return ''
    graph=[]
    for p,op,r in rows:
        if op=='CI':ends=[dispatch(inc(p))]
        elif op=='CD':ends=[dispatch(inc(leave(p,'0',1))),dispatch(inc(p))]
        elif op=='CB':ends=[dispatch(inc(leave(p,'0',r)))]
        elif op=='CC':ends=[dispatch(leave(p,'1',r))]
        else:ends=[]
        graph.append([op,r,ends])
    check(dispatch('')==0,'incorrect entry ordinal')
    return graph,checks

def compare(reference,candidate):
    files=[];graphs=[];rr=[]
    for p in (reference,candidate):
        raw=Path(p).read_bytes();rows=json.loads(raw);trie,count=build(rows)
        graph=scoped_graph(rows,trie);counter,checks=counter_graph(rows)
        check(graph==counter,'resolver disagreement')
        graphs.append(graph);rr.append(rows)
        files.append({'path':str(p),'sha256':digest(raw),'canonical_sha256':digest(canonical(rows)),
         'primitives':len(rows),'dag_nodes':count,'guarded_edges':sum(len(x[2])for x in graph),
         'guarded_cases_including_halt':sum(max(1,len(x[2]))for x in graph),
         'dispatch_checks':checks,'maximum_depth':max(len(x[0])for x in rows),
         'maximum_zero_run':max(len(z)for x in rows for z in x[0].split('1'))})
    check([r[1:]for r in rr[0]]==[r[1:]for r in rr[1]],'primitive word mismatch')
    check(graphs[0]==graphs[1],'guarded graph mismatch')
    return {'status':'PASS','inputs':files,'guarded_graph_sha256':digest(canonical(graphs[0])),
     'identical_paths':sum(a[0]==b[0]for a,b in zip(*rr)),
     'scope':'Source configurations at the same primitive ordinal and the same arbitrary nine natural register values form a strong step-for-step bisimulation. No bound on registers or execution lengths is used. This does not certify a binary transition table, its runtime, its tape invariant, its blank initialization, or foundational consistency calibration.'}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--reference',required=True);ap.add_argument('--candidate',required=True);ap.add_argument('--out',required=True);a=ap.parse_args()
    result=compare(a.reference,a.candidate);result['checker_sha256']=digest(Path(__file__).read_bytes())
    Path(a.out).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

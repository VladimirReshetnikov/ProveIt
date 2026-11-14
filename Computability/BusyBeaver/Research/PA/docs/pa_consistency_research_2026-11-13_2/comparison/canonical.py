"""Exact rooted labelled-graph and ordinal-source comparison."""
from pathlib import Path
from collections import Counter
import hashlib,json

def read_table(path):
    table={};start=0
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):start=int(line.split()[-1]);continue
        if not line or line.startswith('#'):continue
        q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
        if (q,b)in table or b not in (0,1)or w not in(0,1)or d not in('L','R'):
            raise ValueError((path,line))
        table[q,b]=(w,d,n)
    states={q for q,b in table}
    if set(table)!={(q,b)for q in states for b in(0,1)}:raise ValueError('Partial table')
    terminals={n for w,d,n in table.values()}-states
    if len(terminals)!=1:raise ValueError('Unexpected terminal controls')
    return start,states,next(iter(terminals)),table

def canonical(path):
    start,states,halt,table=read_table(path)
    labels={start:0};todo=[start]
    for q in todo:
        for b in(0,1):
            n=table[q,b][2]
            if n!=halt and n not in labels:labels[n]=len(labels);todo.append(n)
    if set(labels)!=states:raise ValueError('Graph-unreachable working states')
    labels[halt]=-1
    rows=[[labels[q],b,w,d,labels[n]]for q in todo for b in(0,1)for w,d,n in[table[q,b]]]
    raw=json.dumps(rows,separators=(',',':')).encode()
    return {'working_states':len(states),'rows':len(table),'halt':halt,
            'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
            'canonical_sha256':hashlib.sha256(raw).hexdigest(),
            'canonical_rows':rows,'canonical_labels':labels}

def source_graph(path):
    sites=json.loads(path.read_text());positions={p:i for i,(p,op,arg) in enumerate(sites)}
    def locate(prefix):
        if prefix in positions:return positions[prefix]
        found=[]
        for i,(p,op,arg) in enumerate(sites):
            if p.startswith(prefix):found.append(i)
            elif prefix.startswith(p) and set(prefix[len(p):])<=set('0'):return i
        if not found:raise ValueError(('unresolved prefix',prefix))
        return min(found)
    def after(prefix):
        at=prefix.rfind('0')
        if at<0:return None
        return locate(prefix[:at]+'1')
    def ancestor(prefix,bit,k):
        loc=[i for i,b in enumerate(prefix) if b==bit]
        if k>len(loc):raise ValueError('Insufficient branch depth')
        return prefix[:loc[-k]] if k else prefix
    graph=[]
    for p,op,arg in sites:
        if op=='CI':row=(op,arg,after(p))
        elif op=='CD':row=(op,arg,after(ancestor(p,'0',1)),after(p))
        elif op=='CB':row=('jump',after(ancestor(p,'0',arg)))
        elif op=='CC':row=('jump',locate(ancestor(p,'1',arg)))
        elif op in ('CH','H'):row=('halt',)
        else:raise ValueError(op)
        graph.append(row)
    return sites,graph

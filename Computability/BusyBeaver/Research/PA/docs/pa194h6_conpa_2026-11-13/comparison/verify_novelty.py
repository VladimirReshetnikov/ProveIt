#!/usr/bin/env python3
"""Exact action-graph novelty against the 34 current 194-state classes.

The comparison does not infer a consistency theorem. It quotients by arbitrary
state relabeling, changes of graph-spanning root, global L/R exchange, and global
read/write symbol exchange. It compares canonical tuples; SHA-256 is display-only.
A zero/one exchange need not preserve zero-blank semantics: allowing it makes the
absence-of-match statement stronger as a finite graph distinction.
"""
from pathlib import Path
import argparse,hashlib,json,re

def parse(data):
    rows={};declared=None
    for line in data.decode('ascii').splitlines():
        line=line.strip()
        if not line:continue
        if line.startswith('#'):
            m=re.search(r'\bstart\s*(\d+)',line,re.I)
            if m and declared is None:declared=int(m[1])
            continue
        pieces=line.split()
        if len(pieces)!=5:raise ValueError('Not a five-column numeric table')
        q,b,w,d,n=pieces;q,b,w,n=map(int,(q,b,w,n))
        if b not in (0,1) or w not in (0,1) or d not in ('L','R') or (q,b) in rows:raise ValueError('Invalid transition')
        rows[q,b]=(w,d,n)
    states={q for q,b in rows}
    if not states or len(rows)!=2*len(states) or any((q,b) not in rows for q in states for b in (0,1)):raise ValueError('Incomplete state')
    halts={n for w,d,n in rows.values()}-states
    if len(halts)!=1:raise ValueError('Expected one terminal control')
    if declared is None and states==set(range(len(states))):declared=0
    if declared is not None and declared not in states:raise ValueError('Invalid start')
    return rows,states,declared

def rooted(rows,states,start,mirror=False,swap=False):
    order=[start];index={start:0};code=[]
    for q in order:
        for b in (0,1):
            w,d,n=rows[q,b ^ swap]
            if n in states:
                if n not in index:index[n]=len(order);order.append(n)
                target=index[n]
            else:target=-1
            code.extend((w ^ swap, int(d=='R') ^ mirror, target))
    return tuple(code),len(order)

def canonical(data):
    rows,states,start=parse(data)
    best=None;spanning=0
    for q in states:
        code,count=rooted(rows,states,q)
        if count!=len(states):continue
        spanning+=1
        for mirror,swap in ((0,0),(1,0),(0,1),(1,1)):
            code,_=rooted(rows,states,q,mirror,swap)
            if best is None or code<best:best=code
    if best is None:raise ValueError('No graph-spanning root; outside this comparator')
    return best,{'working_states':len(states),'declared_start':start,'spanning_roots':spanning,'reachable_from_declared_start':None if start is None else rooted(rows,states,start)[1]}

def main():
    a=argparse.ArgumentParser(description=__doc__)
    a.add_argument('candidate',type=Path)
    a.add_argument('--frontier',type=Path,default=Path(__file__).resolve().parent/'frontier194.json')
    a.add_argument('--output',type=Path)
    args=a.parse_args();data=args.candidate.read_bytes();key,info=canonical(data)
    rows=json.loads(args.frontier.read_text());matches=[];seen={}
    for rec in rows:
        p=args.frontier.parent/rec['offline_table'];b=p.read_bytes()
        if hashlib.sha256(b).hexdigest()!=rec['representative_sha256']:raise ValueError('Frontier identity mismatch: '+str(p))
        k,i=canonical(b)
        if k in seen:raise ValueError('Frontier duplicate: '+rec['name']+' / '+seen[k])
        seen[k]=rec['name']
        if k==key:matches.append(rec['name'])
    result={'source_commit':'3cc7fbf75ba111a0da696ef2f6001dd528891bd5','candidate_sha256':hashlib.sha256(data).hexdigest(),**info,'prior194_classes':len(rows),'exact_tuple_matches':matches,'novel_within_censused_194_graphs':not matches,'scope':'Arbitrary state renaming, any graph-spanning root, global tape reflection, and global read/write bit exchange. Complete tuples are compared; hashes identify files only.'}
    if args.output:args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()

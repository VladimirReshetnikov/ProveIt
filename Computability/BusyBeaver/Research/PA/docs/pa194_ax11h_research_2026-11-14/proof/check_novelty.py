#!/usr/bin/env python3
"""Exact action-graph comparison, independent of fingerprint equality.

Allow all spanning roots, arbitrary state renaming, global reflection,
global bit exchange, and irrelevant final write/move effects. Bit exchange
is a deliberately stronger structural comparison, not a zero-blank theorem.
"""
import argparse,hashlib,json
from pathlib import Path

def parse(path):
    rows={}
    for line in path.read_text().splitlines():
        if not line.strip() or line.lstrip().startswith('#'):continue
        q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
        if b not in(0,1)or w not in(0,1)or d not in('L','R')or(q,b)in rows:raise ValueError(path)
        rows[q,b]=(w,d,n)
    states={q for q,b in rows}
    if not states or any((q,b)not in rows for q in states for b in(0,1)):raise ValueError(path)
    return rows,states

def rooted(rows,states,start,mirror,complement):
    ids={start:0};order=[start];word=[]
    for q in order:
        for bit in(0,1):
            w,d,n=rows[q,bit^complement]
            if n not in states:word.append((0,0,-1));continue
            if n not in ids:ids[n]=len(order);order.append(n)
            word.append((w^complement,(d=='R')^mirror,ids[n]))
    return tuple(word)if len(order)==len(states)else None

def form(rows,states):
    return min((v for q in states for m,c in((False,False),(True,False),(False,True),(True,True))if(v:=rooted(rows,states,q,m,c))is not None),default=None)

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--candidate',type=Path,required=True);ap.add_argument('--census',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    candidate,states=parse(a.candidate);wanted=form(candidate,states)
    if wanted is None:raise AssertionError('candidate has no spanning root')
    entries=json.loads((a.census/'frontier194.json').read_text());checked=[];matches=[]
    for item in entries:
        p=a.census/'representatives'/(item['table_class']+'.tm')
        rows,qs=parse(p);canonical=form(rows,qs)
        same=canonical==wanted
        checked.append({'name':item['name'],'table_class':item['table_class'],'spanning':canonical is not None,'same':same})
        if same:matches.append(item['name'])
    result={'status':'PASS'if not matches else'DUPLICATE','candidate_sha256':hashlib.sha256(a.candidate.read_bytes()).hexdigest(),
            'working_states':len(states),'frontier_objects':len(entries),'spanning_prior_graphs':sum(x['spanning']for x in checked),'matches':matches,
            'comparison':'Exact canonical tuples, all spanning roots, reflection, bit exchange, arbitrary final write/move effects',
            'candidate_canonical_sha256':hashlib.sha256(repr(wanted).encode()).hexdigest(),'checked':checked}
    a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k!='checked'},indent=2))
if __name__=='__main__':main()

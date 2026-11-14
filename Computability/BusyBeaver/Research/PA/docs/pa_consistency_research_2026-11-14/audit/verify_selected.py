#!/usr/bin/env python3
"""Independent rooted graph census of the 22 selected exact tables."""
from pathlib import Path
from collections import Counter
import hashlib,json
BASE=Path(__file__).resolve().parent

def read(data):
    table={}
    for s in data.decode().splitlines():
        if not s.strip()or s.lstrip().startswith('#'):continue
        a,b,c,d,e=s.split();key=(int(a),int(b))
        if key in table:raise ValueError('duplicate row')
        if int(b)not in(0,1)or int(c)not in(0,1)or d not in('L','R'):raise ValueError('invalid row')
        table[key]=(int(c),d,int(e))
    states={q for q,b in table}
    if set(table)!={(q,b)for q in states for b in(0,1)}:raise ValueError('missing binary row')
    return table,states

def canonical(t,states,start,halt):
    if {n for w,d,n in t.values()}-states!={halt}:raise ValueError('terminal convention')
    numbering={start:0};queue=[start];code=[]
    for q in queue:
        for bit in(0,1):
            w,d,n=t[q,bit]
            if n==halt:k=-1
            else:
                if n not in numbering:numbering[n]=len(queue);queue.append(n)
                k=numbering[n]
            code.append([w,d,k])
    if len(queue)!=len(states):raise ValueError('unreachable graph vertex')
    return hashlib.sha256(json.dumps(code,separators=(',',':')).encode()).hexdigest()

def finite_halt(t,start,halt,limit):
    tape=set();q=start;p=0
    for i in range(limit):
        if q==halt:return i
        w,d,q=t[q,int(p in tape)]
        (tape.add if w else tape.discard)(p)
        p+=1 if d=='R'else-1
    return limit if q==halt else None

def main():
    source=json.loads((BASE/'selected196.json').read_text());keys=[];receipts=[]
    for r in source['tables']:
        data=(BASE/r['local_file']).read_bytes()
        if hashlib.sha256(data).hexdigest()!=r['sha256']:raise ValueError('table hash')
        t,states=read(data)
        if len(states)!=196:raise ValueError('state count')
        key=canonical(t,states,r['start'],r['halt']);keys.append(key)
        record={**r,'working_states':len(states),'rows':len(t),'rooted_canonical_sha256':key}
        if r['status']=='rejected':
            ht=finite_halt(t,r['start'],r['halt'],50000)
            if ht!=43563:raise ValueError(('negative control halt',ht))
            record['blank_halt_steps']=ht
        receipts.append(record)
    if len(keys)!=22 or len(set(keys))!=22:raise ValueError('expected distinct census')
    summary={'source_commit':source['source_commit'],'selected_tables':22,'rooted_graph_classes':22,
     'status_counts':dict(Counter(r['status']for r in receipts)),
     'all_complete_and_graph_reachable':True,'negative_controls_halt_in':43563,
     'proof_scope':'Exact table structure, byte identity, state renaming classification and two finite blank halts. Candidate consistency endpoints and arbitrary runtime contracts are not checked by this program.'}
    result={'summary':summary,'tables':receipts}
    (BASE/'selected196_receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(summary,indent=2))
if __name__=='__main__':main()

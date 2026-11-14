#!/usr/bin/env python3
"""Replay exact novelty against the complete frozen 194-state frontier.

Python standard library only. The comparison allows state renaming, every
graph-spanning root, global tape reflection, global binary-symbol exchange,
and arbitrary actions on the final halting edge. Symbol exchange is a
structural screen only: it need not preserve a zero-blank computation.

The proof-relevant equality check compares complete tuples; hashes only bind
artifact identities. No finite blank-tape run is used as a novelty test.
"""
from pathlib import Path
import argparse,hashlib,json,re

ROOT=Path(__file__).resolve().parent
def digest(data):return hashlib.sha256(data).hexdigest()

def parse(data):
    rows={}
    for line in data.decode('ascii').splitlines():
        line=line.strip()
        if not line or line.startswith('#'):continue
        values=re.split(r'[,\s]+',line)
        if len(values)!=5:raise ValueError('Not a five-column table')
        q,b,w,d,n=values;q,b,w,n=map(int,(q,b,w,n))
        if q<0 or n<0 or b not in (0,1) or w not in (0,1) or d not in ('L','R') or (q,b) in rows:raise ValueError('Invalid transition')
        rows[q,b]=(w,d,n)
    states={q for q,b in rows};halts={n for w,d,n in rows.values()}-states
    if not states or len(halts)!=1 or any((q,b) not in rows for q in states for b in (0,1)):raise ValueError('Not a complete binary one-halt table')
    return rows,states

def spanning_roots(rows,states):
    order=sorted(states);index={q:i for i,q in enumerate(order)}
    reach=[1<<i for i in range(len(order))]
    edges=[[index[n] for b in (0,1) if (n:=rows[q,b][2]) in states] for q in order]
    changed=True
    while changed:
        changed=False
        for i,targets in enumerate(edges):
            updated=reach[i]
            for j in targets:updated|=reach[j]
            if updated!=reach[i]:reach[i]=updated;changed=True
    mask=(1<<len(states))-1
    return [q for q,r in zip(order,reach) if r==mask]

def canonical(rows,states):
    roots=spanning_roots(rows,states)
    if not roots:raise ValueError('No graph-spanning root')
    best=None;witness=None
    for reflected in (False,True):
        for complemented in (False,True):
            for root in roots:
                labels={root:0};order=[root];out=[]
                for q in order:
                    for b in (0,1):
                        w,d,n=rows[q,b^complemented]
                        if n not in states:out.append((0,'R',-1));continue
                        w^=complemented
                        if reflected:d='L' if d=='R' else 'R'
                        if n not in labels:labels[n]=len(order);order.append(n)
                        out.append((w,d,labels[n]))
                form=tuple(out)
                if best is None or form<best:best=form;witness={'root':root,'reflected':reflected,'complemented':complemented}
    return best,witness

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--candidate',type=Path,default=ROOT.parent/'machine/machine.tm')
    ap.add_argument('--receipt',type=Path)
    args=ap.parse_args()
    entries=json.loads((ROOT/'frontier194.json').read_text())
    candidate_bytes=args.candidate.read_bytes();rows,states=parse(candidate_bytes)
    if len(states)!=194:raise ValueError('Candidate is not 194-state')
    candidate,witness=canonical(rows,states);matches=[];classes=set()
    for entry in entries:
        data=(ROOT/entry['table_file']).read_bytes()
        if digest(data)!=entry['table_sha256']:raise ValueError('Reference hash mismatch: '+entry['name'])
        r,s=parse(data)
        if len(s)!=194:raise ValueError('Reference size mismatch')
        old,_=canonical(r,s)
        frozen=tuple(tuple(row) for row in entry['canonical'])
        if old!=frozen:raise ValueError('Frozen canonical mismatch: '+entry['name'])
        if digest(json.dumps(old,separators=(',',':')).encode())!=entry['extended_class_sha256']:raise ValueError('Canonical hash mismatch')
        classes.add(old)
        if old==candidate:matches.append(entry['name'])
    if len(classes)!=len(entries):raise ValueError('Duplicate frozen frontier classes')
    receipt={'status':'PASS' if not matches else 'MATCH_FOUND','candidate_sha256':digest(candidate_bytes),'working_states':len(states),'transition_rows':len(rows),'complete_frontier_classes_compared':len(entries),'exact_tuple_comparison':True,'reference_tables_and_canonicals_recomputed':True,'candidate_canonical_witness':witness,'matches':matches,'statement':'Structural novelty relative to the pinned recognized corpus, not a proof of semantic inequivalence or global priority.'}
    text=json.dumps(receipt,indent=2)+'\n'
    if args.receipt:args.receipt.write_text(text)
    print(text,end='')
    return 0 if not matches else 1

if __name__=='__main__':raise SystemExit(main())

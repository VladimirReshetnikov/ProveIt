#!/usr/bin/env python3
"""Exact finite action-graph comparison, with broad cosmetic equivalences.

Permits arbitrary control renaming, every spanning root, global reflection,
global bit exchange, and arbitrary writes/moves on transitions into halt.
Bit exchange is a structural test, not a zero-blank semantic equivalence.
No hash equality is used in place of an exact canonical-tuple comparison.
"""
from pathlib import Path
import argparse,hashlib,json
from literal_inventory import parse_table

def rooted(data,root,reflect,complement):
    rows,states,halt=data;labels={root:0};todo=[root];out=[]
    for q in todo:
        row=[]
        for bit in (0,1):
            w,d,t=rows[q,bit^complement]
            if t==halt:
                row.append((0,'R',-1));continue
            if t not in labels:labels[t]=len(todo);todo.append(t)
            row.append((w^complement,('R' if d=='L' else 'L') if reflect else d,labels[t]))
        out.append(tuple(row))
    return tuple(out) if len(todo)==len(states) else None

def canonical(data):
    ans=None; witness=None
    for reflect,complement in ((False,False),(True,False),(False,True),(True,True)):
        for q in sorted(data[1]):
            c=rooted(data,q,reflect,complement)
            if c is not None and (ans is None or c<ans):
                ans=c;witness=(q,reflect,complement)
    return ans,witness

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('candidate',type=Path);ap.add_argument('frontier',type=Path)
    ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    b=args.candidate.read_bytes();data=parse_table(b)
    assert data is not None
    cand,wit=canonical(data);assert cand is not None
    matches=[];compared=[];excluded=[]
    for p in sorted(args.frontier.glob('*.tm')):
        raw=p.read_bytes();d=parse_table(raw)
        assert d is not None,p
        if len(d[1])!=len(data[1]):continue
        c,w=canonical(d)
        if c is None:excluded.append(str(p));continue
        compared.append(dict(file=p.name,raw_sha256=hashlib.sha256(raw).hexdigest()))
        if c==cand:matches.append(str(p))
    result=dict(candidate=str(args.candidate),candidate_sha256=hashlib.sha256(b).hexdigest(),
        working_states=len(data[1]),rows=len(data[0]),whole_table_spanning=True,
        comparison='exact tuple equality, not hash-only',
        permitted_transformations=['state renaming','any spanning initial root','global tape reflection',
            'global symbol complement','ignore terminal halt-edge write/move'],
        candidate_canonical_witness=wit,
        candidate_cosmetic_fingerprint=hashlib.sha256(repr(cand).encode()).hexdigest(),
        compared_classes=len(compared),matches=matches,excluded_no_spanning_root=excluded,
        distinct_from_all_recognized_classes=not matches,compared=compared)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='compared'},indent=2))

if __name__=='__main__':main()

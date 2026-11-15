#!/usr/bin/env python3
"""Portable exact graph-novelty replay against the pinned PA 194-state frontier.

Usage: python3 verify_novelty.py path/to/candidate.tm --output result.json
No external modules or repository checkout are needed. The accompanying
representatives.json and tables/*.tm are the complete comparison inputs.

All state renamings, every spanning initial root, tape reflection, global symbol
exchange, and arbitrary terminal write/move are allowed. Symbol exchange is a
structural comparison, not an assertion of zero-blank semantic equivalence.
Exact canonical tuples are compared; SHA256 is used only to bind input files
and to supply human-readable result fingerprints.
"""
from pathlib import Path
import argparse,hashlib,json

def digest(data):return hashlib.sha256(data).hexdigest()

def parse(data):
    rows={}
    for line in data.decode('ascii').splitlines():
        if not line.strip() or line.lstrip().startswith('#'):continue
        q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t))
        assert b in (0,1) and w in (0,1) and d in ('L','R')
        assert (q,b) not in rows
        rows[q,b]=(w,d,t)
    states={q for q,b in rows}
    assert states and set(rows)=={(q,b) for q in states for b in (0,1)}
    assert len({t for w,d,t in rows.values()}-states)==1
    return rows,states

def canonical(data):
    rows,states=parse(data);best=witness=None
    for reflect,complement in ((0,0),(1,0),(0,1),(1,1)):
        for root in sorted(states):
            labels={root:0};todo=[root];result=[];comparison=0;discard=False
            for q in todo:
                row=[]
                for bit in (0,1):
                    w,d,t=rows[q,bit^complement]
                    if t not in states:
                        row.append((0,'R',-1));continue
                    if t not in labels:labels[t]=len(todo);todo.append(t)
                    row.append((w^complement,('R' if d=='L' else 'L') if reflect else d,labels[t]))
                value=tuple(row)
                if best is not None and comparison==0:
                    comparison=(value>best[len(result)])-(value<best[len(result)])
                    if comparison>0:
                        discard=True;break
                result.append(value)
            if not discard and len(todo)==len(states):
                value=tuple(result)
                if best is None or value<best:best,witness=value,(root,reflect,complement)
    return best,witness

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('candidate',type=Path)
    ap.add_argument('--corpus',type=Path,default=Path(__file__).resolve().parent)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();manifest=json.loads((args.corpus/'representatives.json').read_text())
    raw=args.candidate.read_bytes();candidate,witness=canonical(raw)
    assert candidate is not None,'Candidate must have a spanning root for this exact classifier.'
    count=len(parse(raw)[1]);compared=[];nonspanning=[];matches=[]
    for r in manifest['tables']:
        b=(args.corpus/r['file']).read_bytes()
        assert digest(b)==r['sha256'],r['file']
        assert len(parse(b)[1])==194
        if count!=194:continue
        other,wit=canonical(b)
        item=dict(file=r['file'],sha256=r['sha256'],catalog_class=r['catalog_class'])
        if other is None:
            nonspanning.append(item);continue
        compared.append(item)
        if other==candidate:matches.append(item)
    result=dict(status='PASS' if not matches else 'MATCH FOUND',
        pinned_commit=manifest['pinned_commit'],candidate=args.candidate.as_posix(),
        candidate_sha256=digest(raw),working_states=count,exact_tuple_comparison=True,
        candidate_canonical_witness=witness,candidate_cosmetic_fingerprint=digest(repr(candidate).encode()),
        permitted_transformations=['arbitrary state renaming','any spanning initial root','global tape reflection','global bit exchange','ignore terminal write/move'],
        symbol_exchange_is_only_structural=True,
        compared_labeled_spanning_tables=len(compared),covered_194_catalog_classes=len({r['catalog_class'] for r in compared}),
        excluded_nonspanning_labeled_tables=len(nonspanning),
        nonspanning_exclusion_reason='Existence of a spanning root is invariant under every allowed transformation.',
        matches=matches,distinct_from_entire_recognized_194_literal_frontier=not matches,
        compared=compared,nonspanning=nonspanning)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('compared','nonspanning')},indent=2))

if __name__=='__main__':main()

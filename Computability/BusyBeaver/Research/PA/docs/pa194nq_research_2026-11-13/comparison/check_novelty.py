#!/usr/bin/env python3
"""Exact conservative graph novelty check against all 34 current 194-state classes.

Checks state renaming, arbitrary spanning root, optional reflection and global
symbol exchange by comparing complete canonical tuples, not hash values alone.
This tests literal structural novelty only; material semantic novelty requires a
separate source/command argument. The corpus includes rejected and research tables.
"""
import argparse, hashlib, importlib.util, json, pathlib
ROOT=pathlib.Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('machine_classes',ROOT/'machine_classes_source.py')
mc=importlib.util.module_from_spec(spec);spec.loader.exec_module(mc)

def canonical(rows,states,root,reflect=False,complement=False):
    labels={root:0};queue=[root];out=[]
    for q in queue:
        for b in (0,1):
            w,d,n=rows[q,b^int(complement)]
            if n in states:
                if n not in labels:labels[n]=len(queue);queue.append(n)
                t=labels[n]
            else:t=-1
            out.append((w^int(complement),('R' if d=='L' else 'L') if reflect else d,t))
    return tuple(out) if len(queue)==len(states) else None

def forms(blob,cosmetic=False):
    rows,states,start=mc.parse(blob)
    options=((False,False),(True,False),(False,True),(True,True)) if cosmetic else ((False,False),)
    f=[s for r,c in options for q in states if (s:=canonical(rows,states,q,r,c)) is not None]
    if not f:raise ValueError('No graph-spanning root; this comparator requires a connected reachable machine')
    return min(f)

def audit(candidate):
    blob=candidate.read_bytes();r,states,start=mc.parse(blob)
    plain=forms(blob);wide=forms(blob,True)
    frontier=json.loads((ROOT/'frontier194.json').read_text())
    exact=[];cosmetic=[]
    for item in frontier:
        if item['states']!=len(states):continue
        old=(ROOT/item['comparison_table']).read_bytes()
        if hashlib.sha256(old).hexdigest()!=item['sha256']:raise ValueError('Frozen corpus hash mismatch: '+item['name'])
        if forms(old)==plain:exact.append(item['name'])
        if forms(old,True)==wide:cosmetic.append(item['name'])
    return dict(snapshot='3cc7fbf75ba111a0da696ef2f6001dd528891bd5',candidate=str(candidate),sha256=hashlib.sha256(blob).hexdigest(),working_states=len(states),declared_or_dense_start=start,prior_194_classes=len(frontier),exact_graph_matches=exact,reflection_or_symbol_exchange_matches=cosmetic,structurally_absent=not cosmetic,scope='Complete tuples at every graph-spanning root; state renaming/reflection/global symbol exchange. Semantic materiality and PA equivalence are separate obligations.')

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('candidate',type=pathlib.Path);ap.add_argument('--output',type=pathlib.Path);a=ap.parse_args()
    ans=audit(a.candidate.resolve());out=json.dumps(ans,indent=2)+'\n'
    if a.output:a.output.write_text(out)
    print(out)

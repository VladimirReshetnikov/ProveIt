#!/usr/bin/env python3
"""Recount lookup visits from the exact delivered certificate, not execution time.
This is a finite data audit; the semantic theorem is checked by Coq/Rocq.
"""
from pathlib import Path
import argparse, hashlib, json, re
ROOT=Path(__file__).resolve().parent

def parse_program(path, table, root):
    text=path.read_text()
    if table=='p215_tab':
        body=text.split('Definition p215_tab :',1)[1].split(':= [',1)[1].split('].',1)[0]
        entries=re.findall(r'\((C[NIDBC] \d+|CH), (C[NIDBC] \d+|CH)\)',body)
        rest=re.sub(r'\((C[NIDBC] \d+|CH), (C[NIDBC] \d+|CH)\)', '', body)
        assert re.fullmatch(r'[;\s]*',rest)
        assert len(entries)==179
        aliases={'CN':'N','CI':'I','CD':'D','CB':'B','CC':'C','CH':'H'}
    else:
        entries=[]
        for n,a,b in re.findall(r'\| (\d+) => \((E\w+(?: \d+)?), (E\w+(?: \d+)?)\)',text):
            assert int(n)==len(entries)
            entries.append((a,b))
        assert len(entries)==487
        aliases={'ENode':'N','EInc':'I','EDecnz':'D','EBreak':'B','EContinue':'C','EHalt':'H'}
    def edge(s):
        parts=s.split()
        return aliases[parts[0]], int(parts[1]) if len(parts)==2 else None
    return [tuple(map(edge,row)) for row in entries],root

def site(program, packed):
    nodes,n=program
    bits=[]
    while packed!=1:
        assert packed>1
        bits.append(packed&1);packed>>=1
    for d in range(len(nodes)+1):
        bit=bits[d] if d<len(bits) else 0
        kind,arg=nodes[n][bit] if 0<=n<len(nodes) else ('H',None)
        if kind!='N':return kind,arg
        n=arg
    raise AssertionError('program path exhausted')

def depth(n,j):
    assert 0<=j<n
    d=1
    while n>1:
        k=n//2
        if j<k:n=k
        else:j-=k;n-=k
        d+=1
    return d

def compute():
    text=(ROOT/'NormalizedCert215.v').read_text()
    rows=[tuple(map(int,x)) for x in re.findall(r'\((\d+)%positive,(\d+)%positive,(\d+)%N,(\d+)%N\)',text)]
    assert len(rows)==1426
    p=parse_program(ROOT/'deps/K215F/Prog215.v','p215_tab',178)
    q=parse_program(ROOT/'deps/K215F/DagPerm.v','dag_nodes',0)
    lookups=[0];halts=[]
    for i,(a,b,j,k) in enumerate(rows):
        left,right=site(p,a),site(q,b)
        assert left==right, (i,left,right)
        if left[0]=='H':halts.append(i)
        else:
            assert left[0]=='D',(i,left)
            lookups.extend((j,k))
    assert halts==[19]
    depths=[depth(len(rows),j) for j in lookups]
    return {'entries':len(rows),'branches':len(lookups),
            'halt_rows_assumed_then_crosschecked':halts,
            'list_index_visits':sum(j+1 for j in lookups),
            'balanced_node_visits':sum(depths),'max_lookup_depth':max(depths)}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check',action='store_true');args=ap.parse_args()
    actual=compute()
    if args.check:assert actual==json.loads((ROOT/'lookup_metrics.json').read_text())
    print(json.dumps(actual,indent=2))
if __name__=='__main__':main()

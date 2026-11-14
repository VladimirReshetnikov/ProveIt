#!/usr/bin/env python3
"""Exact, offline graph novelty against every same-size literal census reference.

The reference tables are re-read and re-canonicalized; recorded graph hashes are
checked, not trusted as a substitute for literal bytes. This is graph comparison,
not a semantic correctness proof. Defaults are relative to this script, not CWD.
"""
from pathlib import Path
import argparse,hashlib,json
HERE=Path(__file__).resolve().parent
PACKAGE=HERE.parent
sha=lambda b:hashlib.sha256(b).hexdigest()

def parse(data):
    rows={}
    for line in data.decode().splitlines():
        p=line.split()
        if not p or p[0].startswith(('#','//',';')):continue
        assert len(p)==5,p
        q,r,w,d,t=p;q=int(q);r=int(r);w=int(w);t=int(t)
        assert q>=0 and t>=0 and r in (0,1) and w in (0,1) and d in ('L','R')
        assert (q,r) not in rows;rows[q,r]=(w,d,t)
    states={q for q,r in rows}
    assert states and set(rows)=={(q,r) for q in states for r in (0,1)}
    halts={t for w,d,t in rows.values()}-states;assert len(halts)==1
    return rows,states,next(iter(halts))

def canonical(table,root,mirror=False,flip=0):
    rows,states,halt=table;labels={root:0};todo=[root];ans=[]
    for q in todo:
        rr=[]
        for bit in (0,1):
            w,d,t=rows[q,bit^flip]
            if t==halt:k=-1
            else:
                if t not in labels:labels[t]=len(todo);todo.append(t)
                k=labels[t]
            rr.append([w^flip,('R' if d=='L' else 'L') if mirror else d,k])
        ans.append(rr)
    if len(todo)!=len(states):return None
    return json.dumps(ans,separators=(',',':')).encode()

def root_free(table,mirror=False,flip=0):
    forms=[c for q in sorted(table[1]) if (c:=canonical(table,q,mirror,flip)) is not None]
    assert forms,'No single root reaches every working state; disconnected controls are outside this canonicalizer.'
    return min(forms)

def display(path):
    try:return path.resolve().relative_to(PACKAGE).as_posix()
    except ValueError:return str(path.resolve())

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('candidate',type=Path)
    ap.add_argument('--census',type=Path,default=HERE/'census/census.json')
    ap.add_argument('--references',type=Path,default=HERE/'reference194',help='Literal table directory; default contains all 15 existing 194-state byte forms.')
    ap.add_argument('--output',type=Path)
    a=ap.parse_args()
    b=a.candidate.read_bytes();table=parse(b);n=len(table[1])
    census=json.loads(a.census.read_text())
    expected={r['sha256']:r for r in census['raw_tables'] if r['states']==n}
    signatures={f'mirror={mirror},bitflip={flip}':sha(root_free(table,mirror,flip))
                for mirror in (False,True) for flip in (0,1)}
    actual={};matches=[]
    for path in sorted(a.references.glob('*.tm')):
        data=path.read_bytes();reference=parse(data)
        if len(reference[1])!=n:continue
        h=sha(data);assert h in expected,('Unexpected same-size reference',str(path),h)
        graph=sha(root_free(reference));assert graph==expected[h]['root_free_sha256']
        actual[h]=graph
        if graph in signatures.values():matches.append(expected[h])
    assert set(actual)==set(expected),('Missing literal references',sorted(set(expected)-set(actual)))
    result={'candidate':display(a.candidate),'raw_sha256':sha(b),'working_states':n,
            'transition_rows':len(table[0]),'halt':table[2],'source_commit':census['summary']['commit'],
            'root_free_graph_signatures':signatures,'corpus_same_size_byte_forms':len(expected),
            'same_size_root_free_classes':len(set(actual.values())),
            'all_same_size_literal_references_rehashed_and_recanonicalized':True,
            'matches':matches,
            'novel_up_to_state_renaming_root_choice_reflection_and_global_bit_complement':not matches,
            'scope':'Every recognized same-size numeric literal table in the pinned census, including rejected experiments. The census excludes JSON/source-only encodings. Global bit exchange is a stronger cosmetic check and need not preserve a blank-zero initial tape. This comparison does not establish semantic correctness.'}
    text=json.dumps(result,indent=2)+'\n'
    if a.output:a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(text)
    print(text)
if __name__=='__main__':
    if not __debug__:raise SystemExit('Assertions are required; do not use Python -O.')
    main()

"""Portable exact certificate for the source rotation exposing the 236 fold.

Usage: python verification/check_source_rotation.py --source boundary_source_input.json
       --baseline-table zfc_composed237_old.tm --rotated-table rotated237.tm
       --rotated-sites rotated_sites.json --output source_rotation.json

Only the Python standard library is needed.  Runtime correctness of the four
TM row edits is a separate, complete affine/list check; this file proves the
structured-source equivalence and verifies the literal table edits exactly.
"""
import argparse
from functools import cache
import hashlib
import json
import sys
from pathlib import Path

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('Run with Python assertions enabled')


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read_table(path):
    table={}
    for line in Path(path).read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,n=line.split()
        key=(int(q),int(b))
        assert key not in table and d in ('L','R')
        table[key]=(int(w),d,int(n))
    assert len(table)==474
    assert all((q,1-b) in table for q,b in table)
    return table


def main():
    ap=argparse.ArgumentParser()
    for name in ('source','baseline-table','rotated-table','rotated-sites','output'):
        ap.add_argument('--'+name,required=True)
    args=ap.parse_args()
    data=json.loads(Path(args.source).read_text())
    S=[tuple(x) for x in data['structures']]
    oldroot=data['root'];intern={x:i for i,x in enumerate(S)}
    assert S[234]==(233,123) and S[123]==(122,115)
    def cons(a,b):
        if (a,b) not in intern:
            intern[a,b]=len(S);S.append((a,b))
        return intern[a,b]
    @cache
    def leaves(n):
        x=S[n]
        if isinstance(x[0],str):return (('',*x),)
        return tuple((str(b)+p,o,r) for b in (0,1) for p,o,r in leaves(x[b]))
    @cache
    def boundary(n):
        x=S[n]
        if isinstance(x[0],str):
            op,arg=x
            return (1,0,False) if op=='CD' else (arg,0,False) if op=='CB' else (0,arg,False) if op=='CC' else (0,0,op=='CH')
        a,b=map(boundary,x)
        return max(max(a[0]-1,0),b[0]),max(a[1],max(b[1]-1,0)),a[2] or b[2]
    # All three chunks are closed.  Ordinary sequential associativity is
    # therefore valid for arbitrary register values and surrounding contexts.
    for n in (233,122,115):assert boundary(n)==(0,0,False)
    alt=cons(cons(233,122),115)
    @cache
    def transform(n):
        if n==234:return alt
        return n if isinstance(S[n][0],str) else cons(*map(transform,S[n]))
    newroot=transform(oldroot)
    oldsites=leaves(oldroot);newsites=leaves(newroot)
    assert list(map(list,newsites))==json.loads(Path(args.rotated_sites).read_text())

    def signature(rows):
        # Independent ordered-CFG construction from complete leaf paths.
        intervals={}
        for i,(path,_,_) in enumerate(rows):
            for k in range(len(path)+1):
                p=path[:k]
                if p not in intervals:intervals[p]=[i,i+1]
                else:intervals[p][1]=i+1
        def jump(path,k,bit):
            cuts=[i for i,b in enumerate(path) if b==bit]
            if len(cuts)<k:return ('break' if bit=='0' else 'continue',k-len(cuts))
            target=intervals[path[:cuts[-k]]][1 if bit=='0' else 0]
            return ('break',0) if target==len(rows) else target
        out=[]
        for i,(path,op,arg) in enumerate(rows):
            nxt=i+1 if i+1<len(rows) else ('break',0)
            dest=(nxt,) if op=='CI' else (jump(path,1,'0'),nxt) if op=='CD' else (jump(path,arg,'0'),) if op=='CB' else (jump(path,arg,'1'),) if op=='CC' else ('halt',)
            out.append((op,arg,dest))
        return out
    assert len(oldsites)==len(newsites)==6455
    assert signature(oldsites)==signature(newsites)
    old=read_table(args.baseline_table);new=read_table(args.rotated_table)
    assert old.keys()==new.keys()
    actual={k:(old[k],new[k]) for k in old if old[k]!=new[k]}
    expected={
        (177,0):((0,'R',165),(0,'R',185)),
        (177,1):((1,'R',185),(1,'R',212)),
        (185,0):((0,'R',192),(0,'R',165)),
        (185,1):((1,'R',212),(1,'R',192)),
    }
    assert actual==expected
    prefixes=[]
    def occurrences(n,p):
        if n==234:prefixes.append(p)
        if isinstance(S[n][0],int):
            for b,ch in enumerate(S[n]):occurrences(ch,p+str(b))
    occurrences(oldroot,'')
    result=dict(status='PASS_EXACT_SOURCE_ROTATION_AND_LITERAL_ROW_EDITS',
        source_sha256=digest(args.source),baseline_table_sha256=digest(args.baseline_table),
        rotated_table_sha256=digest(args.rotated_table),rotated_sites_sha256=digest(args.rotated_sites),
        old_subtree=234,chunks=[233,122,115],closed_chunks=True,
        chunk_leaf_counts=[len(leaves(n)) for n in (233,122,115)],
        occurrence_prefixes=prefixes,sites=len(newsites),guarded_cases=8386,
        changed_paths=sum(a[0]!=b[0] for a,b in zip(oldsites,newsites)),
        ordered_operation_and_successor_signature_identical=True,
        row_edits=[dict(state=q,read=b,before=a,after=z) for (q,b),(a,z) in actual.items()])
    Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()

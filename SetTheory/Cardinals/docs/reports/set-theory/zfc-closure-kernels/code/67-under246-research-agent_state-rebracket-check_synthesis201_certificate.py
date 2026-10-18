#!/usr/bin/env python3
"""Independent standard-library partition check; optional affine-leaf replay."""
import argparse,gzip,json,hashlib,itertools
from pathlib import Path
if not __debug__:
    raise RuntimeError('Run with Python assertions enabled; do not use -O or -OO.')
HERE=Path(__file__).resolve().parent

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--replay',action='store_true');args=ap.parse_args()
    raw=gzip.decompress((HERE/'synthesis201_three_rows.json.gz').read_bytes());d=json.loads(raw)
    assert d['status']=='COMPLETE'
    actions=list(map(tuple,d['actions']));keys=list(map(tuple,d['rows']));tree=d['tree'];seen=set()
    assert len(set(actions))==len(actions)==984
    assert len(set(keys))==len(keys)==3
    assert all(w in (0,1) and m in ('L','R') and isinstance(q,str) for w,m,q in actions)
    targets={a[2] for a in actions};assert set(actions)==set(itertools.product((0,1),('L','R'),targets))
    leaf_hist={};split_hist={};replays=0
    if args.replay:
        import sys
        sys.path.insert(0,str(HERE.parents[1]/'root_search'))
        import compile201
        from search_repair import cases,run
        n,r,t=compile201.build();t['243',0]=(0,'R','113');t['243',1]=(1,'R','218');cc=list(cases(n,r))
        assert targets=={q for q,b in t}|{'254'}

    def visit(i,assigned):
        nonlocal replays
        assert isinstance(i,int) and 0<=i<len(tree) and i not in seen
        seen.add(i);node=tree[i]
        if 'split' in node:
            j=node['split'];assert isinstance(j,int) and 0<=j<len(keys) and j not in assigned
            kids=node['children'];assert len(kids)==len(actions)
            split_hist[j]=split_hist.get(j,0)+1
            return sum(visit(child,{**assigned,j:a}) for a,child in enumerate(kids))
        assert 'reject' in node and 'accept' not in node
        assert isinstance(node['reject'],int) and 0<=node['reject']<d['cases']
        expected=len(actions)**(len(keys)-len(assigned));assert node['completions']==expected
        leaf_hist[node['reject']]=leaf_hist.get(node['reject'],0)+1
        if args.replay:
            # Unassigned rows are forbidden: rejection must occur before one is read.
            class Unassigned(Exception):pass
            class Replay(dict):
                def __getitem__(self,k):
                    if k in keys:
                        j=keys.index(k)
                        if j not in assigned:raise Unassigned(k)
                        return actions[assigned[j]]
                    return super().__getitem__(k)
            try:run(Replay(t),cc[node['reject']])
            except (AssertionError,KeyError) as e:assert str(e)==node['message'];replays+=1
            else:raise AssertionError('certificate leaf was accepted')
        return expected

    total=visit(d['root'],{})
    assert len(seen)==len(tree)
    assert total==d['counts']['covered']==d['total_family']==len(actions)**len(keys)
    report=dict(status='PASS',scope=__doc__,raw_sha256=hashlib.sha256(raw).hexdigest(),nodes=len(tree),covered=total,leaf_case_histogram=leaf_hist,split_row_histogram=split_hist,affine_rejections_replayed=replays)
    (HERE/'synthesis201_partition_audit.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()

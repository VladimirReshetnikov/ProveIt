"""Independently replay the lazy search's finite assignment partition.

This checks the complete branching ledger, pruning weights, final frontier,
source family, and per-source totals. It does not rerun symbolic TM traces;
the diagnostic predicate is supplied by the separately recorded search.
"""
from pathlib import Path
from collections import Counter
import argparse,hashlib,json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
BOX={0,1,2,3,4,6,28,31,38,40,43,44,48,56,59,60,63,64,69,73,75,83,85,95,97,109,112,131}

def audit(manifest,journal,table_path):
    result=json.loads(manifest.read_text())
    raw=table_path.read_bytes()
    assert hashlib.sha256(raw).hexdigest()==result['table_sha256']=='939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713'
    table={}
    for line in raw.decode().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split();key=int(q),int(b)
        assert key not in table
        table[key]=int(w),d,int(t)
    states=sorted({q for q,b in table})
    protected={(q,b) for q in BOX for b in (0,1)}-{(3,0)}
    blocked={table[k][2] for k in protected}|{64,96}
    eligible=[q for q in states if q not in blocked and all((q,b)not in protected for b in (0,1))]
    incoming={q:sorted(k for k,(_,_,t)in table.items() if t==q and k[0]!=q) for q in eligible}
    family=sorted((q for q in eligible if len(incoming[q])==2),key=lambda q:(q!=107,q))
    assert family==result['eligible_deletions'] and len(family)==46
    destinations={q:[r for r in states if r!=q] for q in family}
    stack=[(q,{}) for q in reversed(family)]
    nodes=Counter();pruned=Counter();survivors=Counter();outcomes=Counter()
    survivor_assignments=[]
    count=0
    with journal.open() as source:
        for line in source:
            entry=json.loads(line);count+=1
            q,assigned=stack.pop()
            recorded={int(i):r for i,r in entry['assigned_targets'].items()}
            assert entry['deleted_old']==q and recorded==assigned,(count,q,assigned,entry)
            assert all(i in (0,1)and r in destinations[q] for i,r in assigned.items())
            nodes[q]+=1;outcome=entry['outcome'];outcomes[outcome]+=1
            if outcome in ('branch','branch_unused_in_runtime'):
                i=entry['incoming_index']
                assert i in (0,1)and i not in assigned
                for r in reversed(destinations[q]):stack.append((q,{**assigned,i:r}))
            elif outcome=='prune':
                weight=251**(2-len(assigned))
                assert entry['joint_completions']==weight
                assert 0<=entry['first_failure_case']<8391
                assert entry['reason']in ('fuel','unsupported_symbolic_rule','missing_transition')
                pruned[q]+=weight
            elif outcome=='affine_survivor':
                assert len(assigned)==2
                survivors[q]+=1
                survivor_assignments.append((q,tuple(sorted(assigned.items()))))
            else:raise AssertionError(('unknown outcome',outcome))
    expected_frontier=[{'deleted_old':q,'assigned_targets':{str(i):r for i,r in a.items()},
                        'joint_completions':251**(2-len(a))} for q,a in reversed(stack)]
    assert expected_frontier==result['remaining_frontier']
    remaining=sum(f['joint_completions'] for f in expected_frontier)
    assert count==result['partial_nodes_evaluated']
    assert sum(pruned.values())==result['pruned_completions']
    assert sum(survivors.values())==len(result['affine_survivors'])
    assert survivor_assignments==[(e['deleted_old'],tuple(sorted((int(i),r)for i,r in e['assigned_targets'].items()))) for e in result['affine_survivors']]
    assert remaining==result['remaining_joint_assignments']
    assert len(family)*251**2==result['planned_joint_assignments']==sum(pruned.values())+sum(survivors.values())+remaining
    assert sorted(g['deleted_old']for g in result['states'])==sorted(family)
    for group in result['states']:
        q=group['deleted_old']
        assert group['partial_nodes_evaluated']==nodes[q]
        assert group['pruned_completions']==pruned[q]
        assert group['survivors']==survivors[q]
        assert [(int(a),b)for a,b in group['incoming_rows']]==incoming[q]
    assert (result['status']=='completed')==(not stack)
    digest=hashlib.sha256(journal.read_bytes()).hexdigest()
    assert journal.stat().st_size==result['journal']['bytes']
    assert digest==result['journal']['sha256']
    return {'status':'PASS','scope':__doc__,'table_sha256':result['table_sha256'],
       'journal_sha256':digest,'journal_entries':count,'outcomes':dict(outcomes),
       'concrete_assignments':result['planned_joint_assignments'],
       'pruned_assignments':sum(pruned.values()),'survivor_assignments':sum(survivors.values()),
       'remaining_assignments':remaining,'remaining_frontier_nodes':len(stack),
       'driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
       'replayed_symbolic_Turing_traces':False}

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest',type=Path,required=True)
    parser.add_argument('--journal',type=Path,required=True)
    parser.add_argument('--table',type=Path,default=ROOT/'upstream/Computability/BusyBeaver/Research/ZFC/candidate-permutation252/zfc_permutation252_old.tm')
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    if not __debug__:parser.error('Assertions must remain enabled')
    result=audit(args.manifest,args.journal,args.table)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

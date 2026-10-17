#!/usr/bin/env python3
"""Independent replay of the new joint-action search partition journals.

This verifies exact assignment coverage and the recorded final frontier, not
the semantic outcome of each symbolic diagnostic. It does not import or call
the search driver.
"""
import argparse
import gzip
import hashlib
import itertools
import json
from pathlib import Path

def audit(path):
    result=json.loads(path.read_text())
    dead=result['dead']
    states=[q for q in range(254) if q not in (5,8,dead)]
    actions=list(itertools.product((0,1),('L','R'),[str(q) for q in states]+['254']))
    assert len(states)==251 and len(actions)==1008
    stack=[{}];pruned=0;survivors=[];nodes=0
    journal=path.with_suffix('.jsonl')
    if journal.exists():stream=journal.open()
    else:journal=Path(str(journal)+'.gz');stream=gzip.open(journal,'rt')
    with stream:
        for line in stream:
            item=json.loads(line)
            assigned={int(k):tuple(v) for k,v in item['assignment'].items()}
            assert assigned==stack.pop(),(path,nodes,'assignment_order')
            assert all(k in (0,1) and v in actions for k,v in assigned.items())
            outcome=item['outcome'];nodes+=1
            if outcome.startswith('branch'):
                index=item['index'];assert index in (0,1) and index not in assigned
                stack.extend({**assigned,index:action} for action in reversed(actions))
            elif outcome=='prune':
                weight=1008**(2-len(assigned))
                assert weight==item['completions'] and 0<=item['case']<8391
                pruned+=weight
            elif outcome=='survivor':
                assert len(assigned)==2
                survivors.append(item)
            else:raise AssertionError(outcome)
    expected=[{int(k):tuple(v) for k,v in x.items()} for x in result['frontier']]
    assert stack==expected
    remaining=sum(1008**(2-len(x)) for x in stack)
    assert pruned==result['pruned'] and remaining==result['remaining']
    assert pruned+remaining+len(survivors)==1008**2==result['planned']
    assert len(survivors)==len(result['survivors']) and nodes==result['evaluated_nodes']
    return dict(deleted_state=dead,status='PASS',nodes=nodes,pruned=pruned,
                remaining=remaining,survivors=len(survivors),
                journal=journal.name,journal_sha256=hashlib.sha256(journal.read_bytes()).hexdigest(),
                result_sha256=hashlib.sha256(path.read_bytes()).hexdigest())

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('results',nargs='+',type=Path)
    ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args()
    checks=[audit(p) for p in a.results]
    output=dict(scope='Independent exact journal partition and frontier replay; affine outcomes are not rerun.',
                status='PASS',results=checks,total_pruned=sum(r['pruned'] for r in checks),
                total_remaining=sum(r['remaining'] for r in checks))
    a.output.write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps(output))

if __name__=='__main__':main()

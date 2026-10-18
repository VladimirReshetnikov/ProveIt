#!/usr/bin/env python3
"""Replay a complete lazy-search partition, optionally compare Python control.

This checks traversal and counted coverage only; it does not rerun the affine
semantics for recorded failures. The separate unchanged-Python replay checks
those semantics on its stated deterministic sample.
"""
import argparse, csv, hashlib, json
from collections import Counter, defaultdict
from pathlib import Path

def main():
    p=argparse.ArgumentParser();p.add_argument('--ledger',type=Path,required=True)
    p.add_argument('--data',type=Path,required=True);p.add_argument('--actions',type=int,default=1008)
    p.add_argument('--python-journal',type=Path);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();assert a.actions in(251,1008)
    family=[]
    for line in(a.data/'family.tsv').read_text().splitlines():
        x=list(map(int,line.split()));family.append((x[0],[(x[1],x[2]),(x[3],x[4])]))
    states=sorted({int(l.split()[0])for l in(a.data/'baseline.tm').read_text().splitlines()if l and not l.startswith('#')})
    python_by_dead=defaultdict(list)
    if a.python_journal:
        assert a.actions==251
        for line in a.python_journal.open():
            v=json.loads(line);python_by_dead[v['deleted_old']].append(v)
    counts=Counter();by_group=[];active=-1;stack=[];matched=0;branches=0;python_index=0
    for v in csv.DictReader(a.ledger.open(),delimiter='\t'):
        group,dead,a0,a1=map(int,(v['group'],v['deleted'],v['a0'],v['a1']))
        if group!=active:
            assert not stack,('unfinished_previous_group',active)
            if active>=0:
                assert pruned+good==a.actions**2
                by_group.append({'group':active,'deleted':family[active][0],'pruned':pruned,'survivors':good,'nodes':nodes,'branches':branches})
                if a.python_journal:assert python_index==len(python_by_dead[family[active][0]])
            assert group==active+1;active=group;stack=[(-1,-1)];pruned=good=nodes=branches=python_index=0
        assert dead==family[group][0]
        assert stack and stack.pop()==(a0,a1),('traversal_mismatch',group,a0,a1)
        assert all(-1<=x<a.actions for x in(a0,a1));nodes+=1
        outcome=v['outcome'];index=int(v['case_or_needed']);reason=int(v['reason']);weight=int(v['weight'])
        if outcome=='branch':
            assert index in(0,1)and(a0,a1)[index]<0 and weight==0 and reason==0
            for k in reversed(range(a.actions)):
                child=[a0,a1];child[index]=k;stack.append(tuple(child))
            branches+=1
        elif outcome=='prune':
            assert 0<=index<8391 and reason in(1,2,3,4,5)
            assert weight==a.actions**sum(x<0 for x in(a0,a1));pruned+=weight
        else:
            assert outcome=='survivor'and min(a0,a1)>=0 and weight==1;good+=1
        counts[outcome]+=1
        if a.python_journal:
            targets=[q for q in states if q!=dead]
            assigned={str(i):targets[x]for i,x in enumerate((a0,a1))if x>=0}
            old=python_by_dead[dead][python_index];python_index+=1
            assert old['assigned_targets']==assigned
            assert old['outcome']==outcome
            if outcome=='branch':assert old['incoming_index']==index
            elif outcome=='prune':
                assert old['first_failure_case']==index and old['joint_completions']==weight
                translated='fuel'if reason==1 else'missing_transition'if reason==4 else'unsupported_symbolic_rule'
                assert old['reason']==translated
            matched+=1
    assert active==len(family)-1 and not stack
    assert pruned+good==a.actions**2
    if a.python_journal:assert python_index==len(python_by_dead[family[active][0]])
    by_group.append({'group':active,'deleted':family[active][0],'pruned':pruned,'survivors':good,'nodes':nodes,'branches':branches})
    result={'status':'PASS','scope':'Complete branch/prune partition and optional exact target-only ledger comparison; no affine failure rerun by this script.',
        'groups':len(by_group),'actions_per_row':a.actions,'planned':len(by_group)*a.actions**2,
        'pruned':sum(x['pruned']for x in by_group),'survivors':sum(x['survivors']for x in by_group),
        'nodes':sum(x['nodes']for x in by_group),'branches':sum(x['branches']for x in by_group),
        'outcomes':dict(counts),'python_entries_matched':matched,
        'ledger_sha256':hashlib.sha256(a.ledger.read_bytes()).hexdigest(),'per_group':by_group}
    a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k!='per_group'}))

if __name__=='__main__':main()

#!/usr/bin/env python3
"""Replay all 181 newly proved source contracts without repeating the search.

Also compares the observed executor with its inherited original on every
8,391 baseline guarded case. This is ordinary symbolic verification built
on the stated protected-box contracts, not a proof-assistant kernel check.
"""
from __future__ import annotations
import argparse,hashlib,json,time
from collections import Counter
from pathlib import Path
import check_countdowns as cc

t=cc.t;c=cc.c;ROOT=cc.ROOT;source=t.source;effects=t.effects
HERE=Path(__file__).resolve().parent

def normal(x):return json.loads(json.dumps(x))

def independent_matrix(rows,bounds):
    answer=[]
    for row in rows:
        constant=row[9];coefficients=[]
        for coefficient,(lo,hi) in zip(row[:9],bounds):
            if lo==hi:constant+=coefficient*lo;coefficients.append(0)
            else:coefficients.append(coefficient)
        answer.append(tuple(coefficients+[constant]))
    return tuple(answer)

def verify():
    start=time.monotonic();effects.install();baseline=0
    for i,(pc,op,reg,zero,branch,target) in enumerate(c.CASES):
        bounds=[(0,None) for _ in range(9)]
        if branch is not None:bounds[branch[0]]=(0,0) if branch[1] else (1,None)
        observed=t.Analyzer(c.T,i,bounds,target,policy='stop',cutpoint_stop=False).run(1000)
        assert observed['status']=='source_target',(i,observed)
        rules,literal=c.strict.run(c.T,pc,branch,target,halt=op=='CH',fuel=1000)
        assert observed['record']=={'rules':dict(rules),'literal_steps':literal}
        baseline+=1
    assert baseline==8391
    traces=json.loads((HERE/'positive_traces/results.json').read_text())
    certificates=json.loads((HERE/'certificates/results.json').read_text())
    remaining=json.loads((HERE/'remaining_cases/results.json').read_text())
    assert traces['counts']=={'blocked':36838,'countdown_shape':9253,'zero_primary_cycle':4193,'other_primary_cycle':1006}
    journal_counts=Counter();journal_total=0
    with (HERE/'positive_traces/journal.jsonl').open() as inp:
        for line in inp:
            row=json.loads(line);journal_counts[row['status']]+=1;journal_total+=1
    assert dict(journal_counts)==traces['counts'] and journal_total==51290
    assert hashlib.sha256((HERE/'positive_traces/journal.jsonl').read_bytes()).hexdigest()==traces['journal_sha256']
    assert hashlib.sha256((HERE/'positive_traces/results.json').read_bytes()).hexdigest()==certificates['input_sha256']
    assert hashlib.sha256((HERE/'certificates/results.json').read_bytes()).hexdigest()==remaining['input_sha256']
    assert len(certificates['results'])==9253
    assert Counter(x['status'] for x in certificates['results'])=={'zero_exit_rejected':14,'binary_countdown_and_clean_exit_verified':9239}
    assert len(certificates['first_contract_survivors'])==138
    assert len(remaining['results'])==138 and not remaining['all_affected_case_survivors']
    assert Counter(x['status'] for x in remaining['results'])=={'rejected_without_countdown':123,'rejected_source_endpoint':15}
    assert sum(x['direct_checks'] for x in remaining['results'])==568
    assert sum(len(x['accelerated'])-1 for x in remaining['results'])==43
    identity=lambda x:(x['deleted'],x['replacement'],x['case'])
    originals={identity(x):x for x in traces['countdown_candidates']}
    proven=[(originals[identity(x)],x) for x in certificates['first_contract_survivors']]
    for item in remaining['fresh_certificates']:
        x=item['certificate']
        if x.get('prefix_covers_original_case') and x.get('matching_full_matrix_source_targets'):
            proven.append((item['trace'],x))
    assert len(proven)==181 and len({identity(x) for x,y in proven})==181
    frontiers,constraints,enabled,_=source.configure(64)
    references=json.loads((HERE/'remaining_cases/matrix_reference_targets.json').read_text())['cases']
    verified=[]
    for expected_trace,expected in proven:
        i=expected['case'];table=c.fold(c.T,str(expected['deleted']),str(expected['replacement']))
        actual_trace=t.Analyzer(table,i,constraints[i],frontiers[i],policy='positive').run(1000)
        assert actual_trace['status']=='countdown_shape'
        assert normal(actual_trace['record'])==expected_trace['record'],('prefix replay',identity(expected))
        candidate={k:expected[k] for k in ('deleted','replacement','case','path')}
        candidate.update(actual_trace)
        actual=cc.check_one(candidate,constraints[i],1000)
        assert actual['status']=='binary_countdown_and_clean_exit_verified'
        for field in ('invariant','counter','cycle_shift','positive_body','zero_exit','prefix_covers_original_case',
                      'prefix_primary_delta','composed_primary_rows'):
            assert normal(actual[field])==expected[field],(identity(expected),field)
        assert actual['prefix_covers_original_case']
        bounds=constraints[i];frame=actual['zero_exit']['record'];reference=references[str(i)]
        assert normal(bounds)==reference['physical_entry_bounds']
        desired=independent_matrix(actual['composed_primary_rows'],bounds)
        matching=[x for x in reference['targets'] if x['pc']==frame['pc'] and x['gap_constant']==frame['gap_constant']
                  and independent_matrix(x['register_affine_rows'],bounds)==desired]
        assert matching,(identity(expected),'source endpoint')
        assert all(x['source_clock_lower_bound']>=1 for x in matching)
        verified.append(list(identity(expected)))
    return {'status':'PASS','scope':__doc__,'baseline_observer_equivalence_cases':baseline,
            'diagnostic_journal_entries':journal_total,'initial_new_contracts':138,
            'additional_new_contracts':43,'replayed_prefix_body_exit_source_contracts':len(proven),
            'verified_contract_identities':verified,'whole_machine_survivors':0,
            'seconds':time.monotonic()-start}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path)
    a=p.parse_args();result=verify()
    if a.output is not None:
        with a.output.open('x') as out:out.write(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('scope','verified_contract_identities')}),flush=True)

if __name__=='__main__':main()

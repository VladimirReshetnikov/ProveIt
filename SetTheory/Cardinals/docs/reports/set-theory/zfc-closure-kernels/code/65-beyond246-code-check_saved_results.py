#!/usr/bin/env python3
"""Independently check saved recipe coverage, source footprints, and SAT traces.

--replay-ledger additionally executes every one-incoming recipe at its saved
first failing case. A checker rejection is not a semantic lower bound.
"""
from pathlib import Path
import argparse, gzip, hashlib, json, time
from collections import Counter
import search_actions as s

EXCLUDED = {8202,8203,8204,8358,8359,8360}

def proof_rows():
    proof=json.loads((s.BASE/'results/macro-inductions.json').read_text())
    result=set()
    def walk(v):
        if isinstance(v,dict):
            if v.get('rule') in ('literal','unary-induction'):
                key=(str(v['state']),v['read'])
                assert s.T[key]==(v['row'][0],v['row'][1],str(v['row'][2]))
                result.add(key)
            for c in v.values():walk(c)
        elif isinstance(v,list):
            for c in v:walk(c)
    walk(proof)
    assert len(result)==42
    return result

def domain(protected):
    states=sorted({q for q,b in s.T},key=int)
    keep={q for q,b in protected}|{s.T[k][2] for k in protected}|{'95','96'}
    singles={}
    doubles={}
    for q in states:
        if q in keep:continue
        incoming=tuple(k for k,row in s.T.items() if row[2]==q and k[0]!=q)
        if any(k in protected for k in incoming):continue
        if len(incoming)==1:singles[q]=incoming[0]
        if len(incoming)==2:doubles[q]=incoming
    assert len(singles)==133 and len(doubles)==46
    return states,singles,doubles

def check_ledger(states,singles,replay):
    records=json.loads((s.ROOT/'experiments/action_search/result.json').read_text())
    assert records['status']=='complete' and records['survivors']==[]
    assert records['stats']['recipes']==130872
    assert set(records['states_completed'])==set(singles)
    seen={q:set() for q in singles}; reasons=Counter();n=0
    with gzip.open(s.ROOT/'experiments/action_search/ledger.jsonl.gz','rt') as f:
        for line in f:
            q,key,action,failed=json.loads(line)
            assert q in singles and tuple(key)==singles[q]
            w,d,r=action
            assert w in (0,1) and d in ('L','R') and r in states+['254'] and r!=q
            assert tuple(action) not in seen[q]
            seen[q].add(tuple(action));n+=1
            assert isinstance(failed,list) and len(failed)==2
            case,error=failed
            assert 0<=case<8391 and isinstance(error,str)
            reasons['fuel' if 'fuel' in error else 'other_checker_rejection']+=1
            if replay:
                mutant={k:v for k,v in s.T.items() if k[0]!=q}
                mutant[tuple(key)]=tuple(action)
                try:s.check(mutant,case)
                except (AssertionError,KeyError) as e:assert str(e)==error,(q,action,case,str(e),error)
                else:raise AssertionError(('recorded failure now accepted',q,action,case))
    for q,actions in seen.items():
        expected={(w,d,r) for w in (0,1) for d in ('L','R') for r in states+['254'] if r!=q}
        assert actions==expected and len(actions)==984
    assert n==130872
    return dict(recipes=n,deleted_states=len(singles),coverage='complete',all_recorded_failures_replayed=replay,rejection_categories=dict(reasons))

def check_two(doubles):
    literal=json.loads((s.ROOT/'context/twoaction-search-summary.json').read_text())
    assert literal['survivors']==0 and literal['pruned_mass']==44539776
    assert {str(x['deleted']) for x in literal['states']}==set(doubles)
    assert len(literal['states'])==46
    for x in literal['states']:
        assert x['planned']==984**2 and x['pruned']+x['survivors']==x['planned']
    assert sum(x['pruned'] for x in literal['states'])==literal['pruned_mass']
    assert sum(x['nodes'] for x in literal['states'])==literal['total_nodes']==5196550
    assert sum(x['checks'] for x in literal['states'])==literal['total_checks']==5216260
    affine=json.loads((s.ROOT/'experiments/two_action_search/result.json').read_text())
    assert affine['status']=='partial' and not affine['survivors']
    assert len(affine['completed'])==14
    assert all(x['complete'] and x['planned']==984**2 and x['stats']['pruned_assignments']==984**2 for x in affine['completed'])
    assert affine['current']['deleted']=='82' and not affine['current']['complete']
    assert affine['current']['stats']['pruned_assignments']==286277
    return dict(literal_complete_recipes=literal['pruned_mass'],literal_states=46,affine_complete_recipes=14*984**2,affine_unfinished_state=82,affine_unfinished_pruned_mass=286277)

def check_detector():
    where=s.ROOT/'experiments/detector_search'
    expected={(9,9):'sat',(8,11):'unsat',(8,13):'unsat',(8,17):'unknown',(8,32):'unknown'}
    for (n,horizon),status in expected.items():
        result=json.loads((where/f'result-{n}-{horizon}.json').read_text())
        assert result['states']==n and result['steps']==horizon and result['status']==status
        if status!='sat':continue
        table={(q,b):(w,1 if d=='R' else -1,t) for q,b,w,d,t in result['rows']}
        assert len(table)==2*n
        assert table[0,0]==(0,-1,1) and table[0,1]==(1,-1,0) and table[1,1]==(1,-1,0)
        assert len(result['traces'])==10
        for r,trace in enumerate(result['traces']):
            initial=(1<<10)|((1<<(9-r)) if r<9 else 0)
            conf=(0,0,initial);goal=(0,-r-1,initial) if r<9 else (n,-9,initial)
            low=-r if r<9 else -8
            assert tuple(trace[0])==conf and len(trace)==horizon+1
            for after in trace[1:]:
                q,h,tape=conf
                if conf!=goal:
                    assert 0<=q<n and low<=h<=1
                    bit=(tape>>(h+9))&1
                    w,move,target=table[q,bit]
                    tape=(tape&~(1<<(h+9)))|(w<<(h+9))
                    conf=(target,h+move,tape)
                assert tuple(after)==conf,(r,after,conf)
            assert conf==goal
    return dict(positive_control='nine-state nine-step model independently replayed',solver_reported_unsat_horizons=[11,13],unresolved_horizons=[17,32],scope='Explicit local reachable-state template and finite horizons; no general lower bound')

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--replay-ledger',action='store_true')
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    if not __debug__:ap.error('Assertions required; do not run with -O.')
    started=time.monotonic()
    assert hashlib.sha256((s.BASE/'machine/zfc_prefix246_old.tm').read_bytes()).hexdigest()=='303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee'
    p=proof_rows();states,singles,doubles=domain(p)
    trace=s.TraceTable(s.T);all_rows=set();allowed_rows=set()
    for i in range(len(s.CASES)):
        trace.used=set();s.check(trace,i);all_rows.update(trace.used)
        if i not in EXCLUDED:allowed_rows.update(trace.used)
    assert len(s.CASES)==8391 and len(all_rows)==472 and all_rows==allowed_rows
    assert p|all_rows==set(s.T) and len(s.T)==492
    out=dict(status='PASS',baseline_cases=8391,macro_support_rows=len(p),literal_rows=len(all_rows),excluded_only_literal_rows=0,combined_rows=len(p|all_rows),one_incoming=check_ledger(states,singles,args.replay_ledger),two_incoming=check_two(doubles),detector=check_detector(),seconds=time.monotonic()-started)
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()

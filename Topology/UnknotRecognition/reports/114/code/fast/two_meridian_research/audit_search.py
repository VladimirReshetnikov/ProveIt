"""Held-out planar inputs and sparse disconnected-rule scaling audit."""
import argparse
from collections import Counter
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import random
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from fastunknot.diagram import Diagram,DiagramError
import fastunknot.two_meridian as native


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args()
    name='fastunknot._seed_audit_baseline'
    spec=importlib.util.spec_from_file_location(name,ROOT/'two_meridian_research/baseline_two_meridian.py')
    old=importlib.util.module_from_spec(spec);sys.modules[name]=old;spec.loader.exec_module(old)
    files=[ROOT/'fastunknot/two_meridian.py',ROOT/'fastunknot/diagram.py',
           ROOT/'fastunknot/integer_codec.py',ROOT/'two_meridian_research/baseline_two_meridian.py',Path(__file__).resolve()]
    def hashes():return {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    before=hashes();start=time.perf_counter();rng=random.Random(261008495)
    uncapped=dict(seconds=None,max_work=None,max_attempts=None)
    cases=[]
    while len(cases)<240:
        strands=rng.randrange(2,8);word=[rng.choice((-1,1))*rng.randrange(1,strands) for _ in range(rng.randrange(strands-1,21))]
        try:d=Diagram.from_braid(strands,word)
        except DiagramError:continue
        previous,current=old.two_meridian_decide(d,**uncapped),native.two_meridian_decide(d,**uncapped)
        assert previous['status']==current['status']
        assert previous.get('certificate')==current.get('certificate')
        if current['status']!='INCONCLUSIVE':
            assert native.verify_two_meridian_certificate(d,current['certificate'],max_work=None)
            assert old.verify_two_meridian_certificate(d,current['certificate'],max_work=None)
        cases.append(dict(strands=strands,word=word,status=current['status'],
                          old_attempts=previous['statistics']['attempts'],
                          statistics=current['statistics']))
    guard_budget=native._Budget(lambda:None,None,None)
    guard_rules,guard_incident=native._rules(4,[(0,0,1,1),(1,2,3,1)],guard_budget)
    assert native._ProductivePairs.build(4,guard_rules,guard_budget) is None
    guard_closure=native._SeedClosures(4,guard_rules,guard_incident,guard_budget)
    assert guard_closure.propagate((0,2))[1]==4
    assert guard_closure.propagate((1,2))[1]==3
    assert guard_closure.propagate((1,3))[1]==3
    scaling=[]
    for blocks in (10,100,1000,5000):
        n=3*blocks;crossings=[(3*j,3*j+1,3*j+2,1) for j in range(blocks)]
        budget=native._Budget(lambda:None,None,None)
        rules,incident=native._rules(n,crossings,budget)
        closures=native._SeedClosures(n,rules,incident,budget)
        candidates=native._ProductivePairs.build(n,rules,budget)
        assert len(candidates.pairs)==2*blocks
        attempts=skipped=0
        for seeds in itertools.combinations(range(n),1):
            attempts+=1;assert closures.propagate(seeds)[1]==1
        for index,seeds in enumerate(candidates.pairs):
            if candidates.excluded[index]:skipped+=1;continue
            attempts+=1;assert closures.propagate(seeds)[1]==3
            candidates.exclude_closed(closures,index,budget)
        assert attempts==4*blocks and skipped==blocks
        assert closures.vertex_pops==6*blocks and closures.rule_visits==8*blocks
        assert candidates.pruning_visits==4*blocks
        scaling.append(dict(blocks=blocks,vertices=n,rules=len(rules),candidate_pairs=len(candidates.pairs),
                            dense_pairs=n*(n-1)//2,attempts=attempts,skipped=skipped,
                            vertex_pops=closures.vertex_pops,rule_visits=closures.rule_visits,
                            pruning_visits=candidates.pruning_visits,work=budget.work))
    assert before==hashes()
    result=dict(seed=261008495,scope='240 held-out actual planar braid closures; synthetic disconnected implication systems for operation scaling, not knot instances',
                cases=cases,counts=dict(Counter(r['status'] for r in cases)),
                search_modes=dict(Counter(r['statistics']['search_mode'] for r in cases)),
                unary_guard_counterexample=dict(crossings=[[0,0,1,1],[1,2,3,1]],
                                                generating_pair=[0,2],naive_candidates_fail=True),
                scaling=scaling,seconds=time.perf_counter()-start,source_sha256=before)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('cases','source_sha256')},indent=2))


if __name__=='__main__':main()

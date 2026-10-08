"""Independent deterministic finite checks; JSON includes exact case counts."""
import json, random, sys, time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path[:0]=[str(ROOT/'src'),str(ROOT/'reference_upstream')]
from closure_reset.diagram import braid_pd,component_count
from closure_reset.cube import Cube, interval_rank, quiver_rank
from closure_reset.driver import recognize_pd,replay
from closure_reset.dots import parity
from closure_reset.binary import rank

def main():
    rng=random.Random(20261007); records=[]; counts=dict(diagrams=0,driver_comparisons=0,interval_comparisons=0,quiver_comparisons=0)
    start=time.perf_counter()
    while len(records)<160:
        s=rng.choice([2,3,4]); n=rng.randrange(1,8)
        w=[rng.choice([-1,1])*rng.randrange(1,s) for _ in range(n)]
        try: pd=braid_pd(s,w)
        except ValueError: continue
        if component_count(pd)!=1: continue
        rng.shuffle(pd); c=Cube(pd,max_crossings=7); c.check(); r=c.homology_rank()
        arms={}
        for name,options in [('full',dict(reset=False,frontier_test=False)),('frontier',dict(reset=False)),('reset',dict(reset=True))]:
            out=recognize_pd(pd,check_d_squared=True,**options)
            assert out['status']==('UNKNOT' if r==2 else 'NONTRIVIAL'),(w,name,out,r)
            counts['driver_comparisons']+=1; arms[name]=out
        if len(records)<12: replay(pd,json.loads(json.dumps(arms['reset'])))
        marks=(c.labels*3)[:3]
        for _ in range(3):
            f=2*rng.randrange(128); l=rng.randrange(1,5)
            assert interval_rank(c,c.polynomial(f,marks),l)==(r if parity(f) else l*r)
            counts['interval_comparisons']+=1
        if n<=6:
            dims=[rng.randrange(1,4) for _ in range(3)]; arrows=[tuple(rng.randrange(1<<b) for _ in range(a)) for a,b in zip(dims,dims[1:])]
            f=2*rng.randrange(128); beta=sum(dims)-sum(rank(a) for a in arrows)
            assert quiver_rank(c,c.polynomial(f,marks),dims,arrows)==r*(beta if parity(f) else sum(dims))
            counts['quiver_comparisons']+=1
        counts['diagrams']+=1
        records.append(dict(strands=s,word=w,pd=pd,rank=r,results=arms))
    summary=dict(seed=20261007,**counts,elapsed_seconds=time.perf_counter()-start,
        reset_cases=sum(x['results']['reset']['stats']['resets']>0 for x in records),
        early_nontrivial=sum(x['results']['reset']['status']=='NONTRIVIAL' and x['results']['reset']['reason']!='complete scalar closure' for x in records),
        nonsingleton_pure_observations=sum(x['results']['reset']['stats']['nonsingleton_pure_blocks'] for x in records),
        nonsingleton_jet_observations=sum(x['results']['reset']['stats']['nonsingleton_jet_blocks'] for x in records),
        all_passed=True,scope='independent cube vs source-derived FastScan fixture; no production-suite claim')
    (ROOT/'results'/'audit_cases.json').write_text(json.dumps(records,indent=2)+'\n')
    (ROOT/'results'/'audit_summary.json').write_text(json.dumps(summary,indent=2)+'\n'); print(json.dumps(summary,indent=2))
if __name__=='__main__': main()

"""Reproducible finite audit. Counts are loop iterations, not test methods."""
import itertools
import json
import platform
import random
import time
from collections import Counter
from math import comb
from pathlib import Path
from envelope_kernel import (Candidate, Envelope, canonical, complementary_pairing,
    count, partitions, reduce_family, refines)
from checker import check_reduction, check_run, direct_compatible, universal_envelopes
from fixtures import random_grammar, wide_envelope
from grammar import compile_envelopes, solve
from surface_replay import replay_pair, replay_witness


def rank(rows):
    pivots={}
    for v in rows:
        while v:
            p=v.bit_length()-1
            if p not in pivots:pivots[p]=v;break
            v^=pivots[p]
    return len(pivots)


def run():
    start=time.perf_counter();rng=random.Random(20261009)
    out={'seed':20261009,'python':platform.python_version(),'platform':platform.platform(),
         'all_checks_passed':False,'envelope_cases':0,'matrix_entries':0,'graded_rank_checks':0,
         'weighted_families':0,'weighted_queries':0,'grammar_triples':0,
         'successful_mesh_replays':0,'random_surface_pairs':0,
         'literal_assignment_grammars':0,'literal_assignments':0,'rank_histogram':{}}
    hist=Counter()
    for r in range(1,7):
        ps=list(partitions(r))
        # All envelope pairs through r=5; all future envelopes with sigma=1 for r=6.
        sigmas=ps if r<=5 else [(0,)*r]
        for sigma in sigmas:
            left=[p for p in ps if refines(p,sigma)]
            for rho in ps:
                right=[q for q in ps if refines(q,rho)]
                env=Envelope(sigma,rho)
                fv={p:env.feature(p) for p in left}
                fq={q:env.feature(q,'future') for q in right}
                rows=[]
                for p in left:
                    row=0
                    for i,q in enumerate(right):
                        direct=direct_compatible(p,q)
                        paired=0 if not env.connected else complementary_pairing(fv[p],fq[q],env.lam)
                        assert direct==paired
                        row|=direct<<i;out['matrix_entries']+=1
                    rows.append(row)
                expected=0 if not env.connected else 1<<env.lam
                assert rank(rows)==expected
                hist[str(expected)]+=1;out['envelope_cases']+=1
                if env.connected:
                    for j in range(env.lam+1):
                        assert rank([row for p,row in zip(left,rows) if count(p)==count(sigma)+j])==comb(env.lam,j)
                        out['graded_rank_checks']+=1
    out['rank_histogram']=dict(sorted(hist.items(),key=lambda x:int(x[0])))
    for _ in range(1000):
        r=rng.randrange(1,7);ps=list(partitions(r))
        sigma=rng.choice(ps);rho=rng.choice(ps);env=Envelope(sigma,rho)
        allowed=[p for p in ps if refines(p,sigma)]
        items=[Candidate(rng.choice(allowed),rng.randrange(-1000,1001),rng.randrange(4),(i,))
               for i in range(rng.randrange(0,70))]
        reduced=reduce_family(items,env)
        ok,why=check_reduction(items,sigma,rho,reduced.certificate)
        assert ok,why
        for q in ps:
            if not refines(q,rho):continue
            for sector in range(4):
                def opt(indices):
                    return min((items[i].cost for i in indices if items[i].sector==sector and direct_compatible(items[i].partition,q)),default=None)
                assert opt(range(len(items)))==opt(reduced.retained)
                out['weighted_queries']+=1
        out['weighted_families']+=1
    for _ in range(600):
        g=random_grammar(rng,max_width=5,depth=rng.randrange(0,4))
        assert compile_envelopes(g)==universal_envelopes(g)
        answers=[]
        for mode in ('exact','root','cycle'):
            answer=solve(g,mode)
            ok,why=check_run(g,answer);assert ok,why
            answers.append((answer['status'],answer['cost_hex']))
            if answer['witness'] is not None:
                assert replay_witness(g,answer['witness'])['disk']
                out['successful_mesh_replays']+=1
        assert len(set(answers))==1
        out['grammar_triples']+=1
    for _ in range(1000):
        r=rng.randrange(1,9)
        p=canonical(rng.randrange(r) for _ in range(r))
        q=canonical(rng.randrange(r) for _ in range(r))
        mesh=replay_pair(p,q,rng.choice((False,True)))
        assert mesh['disk']==direct_compatible(p,q)
        out['random_surface_pairs']+=1
    # Completely enumerate small finite languages and test final mesh topology,
    # without calling any producer transition during the exhaustive baseline.
    for _ in range(40):
        g=random_grammar(rng,max_width=3,depth=rng.randrange(0,3))
        domains=[range(len(g.initial))]+[range(len(l)) for l in g.layers]+[range(len(g.caps))]
        best=None
        for w in itertools.product(*domains):
            out['literal_assignments']+=1
            cost=g.initial[w[0]].cost+g.caps[w[-1]].cost
            sector=g.initial[w[0]].sector^g.caps[w[-1]].sector
            for i,l in enumerate(g.layers):
                cost+=l[w[i+1]].cost;sector^=l[w[i+1]].sector
            mesh=replay_witness(g,w)
            if mesh['disk'] and sector in g.target_sectors and (best is None or cost<best):best=cost
        answer=solve(g)
        assert (None if answer['cost_hex'] is None else int(answer['cost_hex'],16))==best
        out['literal_assignment_grammars']+=1
    env=Envelope(*wide_envelope(256,3))
    items=[Candidate(env.coordinate_partition(j),j) for j in range(8)]
    red=reduce_family(items,env)
    assert len(red.retained)==8 and check_reduction(items,env.sigma,env.rho,red.certificate)[0]
    out['wide_fixture']={'arcs':256,'cycle_rank':3,'retained':8,'checker_passed':True}
    out['all_checks_passed']=True
    out['elapsed_seconds']=time.perf_counter()-start
    return out

if __name__=='__main__':
    output=run()
    Path('results').mkdir(exist_ok=True)
    Path('results/audit.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps(output,indent=2))

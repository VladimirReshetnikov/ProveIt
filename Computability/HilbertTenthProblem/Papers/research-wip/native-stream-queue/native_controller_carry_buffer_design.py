"""Exact periodic-buffer extension, insulation criterion and NAND collision."""
import argparse
from itertools import product
import json
from math import gcd
from pathlib import Path


def run(Q,forcing,start,repeats=1):
    b=start;states=[b];spills=[]
    for _ in range(repeats):
        for g in forcing:
            carry,b=divmod(b+g,Q)
            states.append(b);spills.append(carry)
    return states,spills


def buffers():
    cases=insulated=0
    for Q in range(2,9):
        for T in range(1,6):
            for forcing in product(range(-2,3),repeat=T):
                S=sum(forcing);m=Q//gcd(Q,S)
                partial=[0]
                for g in forcing:partial.append(partial[-1]+g)
                criterion=S==0 and max(partial)-min(partial)<=Q-1
                starts=[]
                for start in range(Q):
                    states,spills=run(Q,forcing,start,m)
                    assert states[-1]==start and sum(spills)==m*S//Q
                    direct,carry=run(Q,forcing,start)
                    if direct[-1]==start and all(k==0 for k in carry):starts.append(start)
                assert bool(starts)==criterion
                expected=list(range(-min(partial),Q-max(partial))) if S==0 else []
                assert starts==expected
                if criterion:
                    assert -min(partial) in starts
                    insulated+=1
                cases+=1
    examples=[]
    for forcing in ((1,1,1,1),(1,1,1,1,-1,-1,-1,-1)):
        results=[]
        for start in range(4):
            states,spills=run(4,forcing,start)
            assert states[-1]==start and any(spills)
            results.append(dict(start=start,states=states,spills=spills))
        examples.append(dict(Q=4,forcing=list(forcing),all_starts=results))
    return dict(forcing_words=cases,insulated_words=insulated,capacities=[2,8],maximum_T=5,examples=examples)


def gates():
    rows=[]
    for b in range(1,11):
        R=2**b;truth=[]
        for a,c in product((0,1),repeat=2):
            v=R+1-a-c
            assert v//R==1-a*c and 0<v<2*R
            truth.append(dict(a=a,b=c,code=v,high_bit=v//R,low=v%R))
        first=(R-1,R+1);second=(R,R)
        assert sum(first)==sum(second)==2*R
        bits1=[v//R for v in first];bits2=[v//R for v in second]
        assert bits1==[0,1] and bits2==[1,1]
        wanted1=1-bits1[0]*bits1[1];wanted2=1-bits2[0]*bits2[1]
        assert wanted1==1 and wanted2==0
        projected=sum(first)//R
        false_code=R+1-projected
        assert projected==2 and false_code//R==0
        rows.append(dict(R=R,truth_table=truth,pair1=list(first),pair2=list(second),
                         identical_sum=2*R,desired_outputs=[wanted1,wanted2],
                         false_projected_code=false_code,extra_low_carry=1))
    return dict(powers_checked=10,domains=rows)


def verify():
    return dict(status='PASS_CARRY_BUFFER_DESIGN_AUDIT',buffers=buffers(),nand=gates(),
                scope='Constructive conditional buffer lemma and falsified equal-weight NAND-code feedback; no generic compiler',
                established_complete_universal_bound=76)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(json.dumps(dict(status=result['status'],forcing_words=result['buffers']['forcing_words'],
                         insulated_words=result['buffers']['insulated_words'],powers=result['nand']['powers_checked']),indent=2))

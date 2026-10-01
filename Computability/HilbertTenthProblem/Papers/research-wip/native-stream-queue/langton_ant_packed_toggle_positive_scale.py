"""Positive-scale successor of the complete packed binary-toggle relation.

The positive-zero coordinate map preserves the supplied-history projection.
Ant motion, input loading and control remain outside this component.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import langton_ant_packed_toggle_tape as parent
import native_binary_positive_scale as scale

PREFIX='native__'


def build():
    old=parent.build()
    packet=scale.rewrite(old,prefix=PREFIX)
    count=Counter('M' if op=='*' else 'A' for _,op,_,_ in packet['source'])
    packet.update(operations=len(packet['source']),multiplications=count['M'],
                  additions_subtractions=count['A'],equations=len(packet['comparisons']),
                  witnesses=len(packet['auxiliaries']))
    assert PREFIX+'w' not in packet['auxiliaries']
    assert packet['interfaces']==old['interfaces']
    assert len(packet['source'])==len(old['source'])==105
    assert len(packet['comparisons'])==17 and len(packet['auxiliaries'])==27
    return packet


polynomial_source=parent.polynomial_source
degree_bound=parent.degree_bound
ledger=parent.ledger


def execute(source,values):
    env=dict(values)
    for name,op,a,b in source:
        assert name not in env
        a=env[a] if isinstance(a,str) else a
        b=env[b] if isinstance(b,str) else b
        env[name]=a*b if op=='*' else a+b if op=='+' else a-b
    return env


def independent_lift(values):
    # Compute the unchanged shared scale directly from the outer coordinates.
    D=values['initial_tape_hat']+values['final_tape_hat']+values['height_slack']
    B=4*D;P=(B-1)*values['J']+1;q=16*B*P**4
    r=values[PREFIX+'r'];b=values[PREFIX+'bound_beta']
    old=dict(values)
    old[PREFIX+'w']=r+b
    old[PREFIX+'bound_beta']=q*(r+b)-r
    return old


def independent_inverse(values):
    result=dict(values)
    result[PREFIX+'bound_beta']=values[PREFIX+'w']-values[PREFIX+'r']
    result.pop(PREFIX+'w')
    return result


def verify():
    old=parent.build();new=build()
    old_source,old_out=polynomial_source(old);source,out=polynomial_source(new)
    old_names={name for name,_,_,_ in old['source']}
    removed=(PREFIX+'bs_X_bound',PREFIX+'wn2')
    assert old['comparisons'].count(removed)==1
    assert new['comparisons']==[pair for pair in old['comparisons'] if pair!=removed]
    assert new['parameters']==old['parameters']
    assert new['auxiliaries']==[n for n in old['auxiliaries'] if n!=PREFIX+'w']
    rng=random.Random(155105)
    identities=signed=positive_lifts=round_trips=0
    for case in range(512):
        positive=case<256
        values={n:rng.randrange(1,9) if positive else rng.randrange(-5,6)
                for n in new['parameters']+new['auxiliaries']}
        lifted=independent_lift(values)
        ne=execute(source,values);oe=parent.execute(old_source,lifted)
        assert ne[out]==oe[old_out]
        for name in old_names-{PREFIX+'bs_X_bound'}:
            assert ne[name]==oe[name],name
        assert oe[removed[0]]==oe[removed[1]]
        assert independent_inverse(lifted)==values
        at=lambda env,x:env[x] if isinstance(x,str) else x
        assert [at(ne,a)-at(ne,b) for a,b in new['comparisons']]==[
            at(oe,a)-at(oe,b) for a,b in old['comparisons'] if (a,b)!=removed]
        # Separate canonical AND invocation audits the inherited scalar interface.
        rr,words,nv=parent.independent(lifted)
        assert ne[out]==sum(r*r for r in rr)
        if positive:
            assert min(lifted.values())>0 and min(words)>=0
            assert ne[PREFIX+'q']>=16
            positive_lifts+=1
        identities+=1;signed+=not positive;round_trips+=1
    # Exact scalar consequences of the complete old kernel; these are not
    # asserted to satisfy every native comparison or form whole Pell zeros.
    inverse_cases=0
    for r in range(1,193):
        q=1<<r.bit_count();X=1<<(2*r+1)
        w=X//q;b=w-r;old_beta=X-r
        assert w>=1<<(r+1)>r and b>0 and old_beta>0
        assert r+b==w and q*(r+b)-r==old_beta
        inverse_cases+=1
    paths=duration_one=erasing_rows=repeated_heads=0
    for duration in range(1,13):
        for case in range(24):
            heads=[1<<rng.randrange(10) for _ in range(duration)]
            if case==0:heads=[1]*duration
            values,trace=parent.positive_path(0 if case<3 else rng.randrange(1024),heads)
            values.pop(PREFIX+'w')
            values[PREFIX+'bound_beta']=rng.randrange(1,8)
            env=execute(new['source'],values)
            assert all(env[a]==env[b] for a,b in new['comparisons'][:2])
            it=new['interfaces']
            A,M,Z=(env[it[k]] for k in ('joined_H','joined_M','joined_Z'))
            assert A&M==Z and max(A,M,Z)<env[it['native_scale']]
            assert min(values.values())>0 and min(independent_lift(values).values())>0
            paths+=1;duration_one+=duration==1
            erasing_rows+=sum(bool(c) for c in trace['reads'])
            repeated_heads+=len(set(heads))<duration
    # Exact circuit degree propagation preserves the old conservative bound.
    assert degree_bound(old)==degree_bound(new)==124
    assert ledger(new)['certificate']==dict(operations=105,multiplications=48,
        additions_subtractions=57,equations=17,witnesses=27)
    ll=ledger(new)['polynomial']
    assert (ll['operations'],ll['multiplications'],ll['additions_subtractions'])==(155,65,90)
    return dict(status='PASS_LANGTON_ANT_PACKED_TOGGLE_POSITIVE_SCALE',ledger=ledger(new),
        complete_source_output_identities=identities,signed_cases=signed,
        positive_lifts=positive_lifts,coordinate_round_trips=round_trips,
        typed_scalar_inverse_cases=inverse_cases,genuine_outer_histories=paths,
        duration_one_histories=duration_one,erasing_rows=erasing_rows,
        repeated_head_histories=repeated_heads,
        source_sha256=hashlib.sha256(json.dumps(source,sort_keys=True).encode()).hexdigest(),
        example=dict(source=source,comparisons=new['comparisons'],parameters=new['parameters'],
                     auxiliaries=new['auxiliaries'],interfaces=new['interfaces'],output=out),
        scope='Positive-zero coordinate bijection with the packed toggle158 parent, preserving '
              'all supplied outer histories; every new positive tuple lifts positively and every '
              'parent positive zero has a positive inverse. Arbitrary signed source identities are '
              'not zero claims. Typed scalar fixtures and outer histories do not materialize full '
              'Pell zeros. Ant motion/control, periodic-background input and acceptance remain unpaid; '
              'the free-head endpoint relation still admits every nonnegative endpoint pair.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['ledger'])

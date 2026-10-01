"""A positive program index removes one gate from the complete U21 compiler.

The effective zero-to-two program map is justified by symbolic infinite loops.
Signed affine graph identities are separate from positive solution semantics.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import korec_packed_counter_units as parent

FORMS=('raw','coupled','fields','range_unit','units')
polynomial_source=parent.polynomial_source
degree_bound=parent.degree_bound
ledger=parent.ledger
execute=parent.execute
PROGRAM='program'
OLD_PROGRAM='program_hat'
SLACK='height_slack'
DELETED='program_69'
PARTIAL='half_height_70'


@lru_cache(None)
def build(form='units'):
    assert form in FORMS
    return rewrite(parent.build(form=form))


def rewrite(old):
    form=old.get('form')
    assert form in FORMS and old==parent.build(form=form),'requires the complete canonical U21 source'
    rows={n:(op,a,b) for n,op,a,b in old['source']}
    assert rows[DELETED]==('-',OLD_PROGRAM,1)
    assert rows[PARTIAL]==('+',OLD_PROGRAM,'input')
    assert [n for n,_,a,b in old['source'] if DELETED in (a,b)]==['initial_program_149']
    assert [n for n,_,a,b in old['source'] if PARTIAL in (a,b)]==['half_height_71']
    alias=lambda v:PROGRAM if v in (DELETED,OLD_PROGRAM) else v
    source=[(n,op,alias(a),alias(b)) for n,op,a,b in old['source'] if n!=DELETED]
    result=parent.ps.metadata(dict(old,source=source,parameters=[PROGRAM,'input'],
        positive_program_index=True,positive_program_parent=old,
        program_recipe='Replace the parent nonnegative program e by e if e>0, otherwise by2.',
        graph_map='old program_hat=program+1, old height_slack=height_slack-1; inverse may be zero or negative off zero.'))
    parent.ps.checked_source(source,result['parameters'],result['auxiliaries'])
    parent.closure(result)
    assert result['operations']==old['operations']-1
    assert result['multiplications']==old['multiplications']
    assert degree_bound(result)==degree_bound(old)
    return result


def to_parent(values):
    assert PROGRAM in values and OLD_PROGRAM not in values
    result=dict(values);result[OLD_PROGRAM]=result.pop(PROGRAM)+1
    result[SLACK]-=1
    return result


def from_parent(values):
    assert OLD_PROGRAM in values and PROGRAM not in values
    result=dict(values);result[PROGRAM]=result.pop(OLD_PROGRAM)-1
    result[SLACK]+=1
    return result


def symbolic_loops():
    """Exact affine tuples c+a*A+x*X; every conditional test is constant."""
    const=lambda c:(c,0,0)
    X=(0,0,1);A=(0,1,0)
    def path(start,steps):
        q,vector=start;vector=list(vector);trace=[]
        for _ in range(steps):
            assert q<len(parent.TABLE),'unexpected halt'
            op,r,*targets=parent.TABLE[q];before=vector[r]
            if op=='I':branch=0
            else:
                assert before[1:]==(0,0),'a symbolic branch would need a separate proof'
                assert before[0]>=0
                branch=int(before[0]==0)
            trace.append((q,branch))
            delta=1 if op=='I' else -1 if op=='D' and branch==0 else 0
            vector[r]=(before[0]+delta,before[1],before[2]);q=targets[branch]
            assert all(min(v)>=0 for v in vector),'nonnegative affine invariant lost'
        return (q,tuple(vector)),trace
    results=[]
    for program,prefix,length in ((0,21,12),(2,59,30)):
        initial=(0,(const(0),const(program),X,const(0),const(0),const(0),const(0),const(0)))
        reached,pt=path(initial,prefix)
        expected=(0,(const(1),const(program),X,const(0),const(0),const(0),const(1),const(0)))
        assert reached==expected
        base=(0,(A,const(program),X,const(0),const(0),const(0),const(1),const(0)))
        end,lt=path(base,length)
        assert end==(0,((1,1,0),const(program),X,const(0),const(0),const(0),const(1),const(0)))
        assert all(parent.TABLE[q][1]!=2 for q,_ in pt+lt)
        results.append(dict(program=program,prefix_steps=prefix,loop_steps=length,
            prefix_edges=pt,loop_edges=lt,start=base,end=end,
            statement='For every X>=0 and A>=0 this loop increments R0 and preserves all other registers; it never reaches halt.'))
    return results


def source_audit(packet,seed,cases=32):
    rng=random.Random(seed);old=packet['positive_program_parent'];nonpositive=0
    for case in range(cases):
        signed=case>=cases//2
        values={n:rng.randrange(-3,4) if signed else rng.randrange(1,5)
                for n in packet['parameters']+packet['auxiliaries']}
        if not signed and case%2==0:values[SLACK]=1
        lifted=to_parent(values);assert from_parent(lifted)==values
        new=execute(packet['source'],values);before=execute(old['source'],lifted)
        assert before[DELETED]==values[PROGRAM]
        assert before[PARTIAL]==new[PARTIAL]+1
        assert all(before[n]==new[n] for n,_,_,_ in packet['source'] if n!=PARTIAL)
        for sos in (False,True):
            ns,no=polynomial_source(packet,sum_of_squares=sos)
            os,oo=polynomial_source(old,sum_of_squares=sos)
            assert execute(ns,values)[no]==execute(os,lifted)[oo]
        nonpositive+=lifted[SLACK]<=0
    return dict(assignments=cases,signed=cases//2,whole_output_identities=2*cases,
                nonpositive_formal_parent_slacks=nonpositive)


def history_audit():
    packet=build();old=packet['positive_program_parent'];histories=rows=0
    outer=[r for r in packet['source'] if not r[0].startswith(('native__','counter_outer_'))]
    for e in range(1,14):
      for x in range(1,5):
        configs,chosen=parent.run(parent.TABLE,e,x,limit=1000)
        if configs[-1][0]!=len(parent.TABLE):continue
        old_values=parent.pack_history(old,configs,chosen,e,x)
        values=from_parent(old_values);assert min(values.values())>0
        env=execute(outer,values);oracle,residuals=parent.direct_outer(old,old_values)
        assert residuals==[-1,0,0] and oracle['ah']&oracle['am']==oracle['az']
        assert all((env[name] if isinstance(name,str) else name)==oracle[key]
                   for key,name in packet['interfaces'].items())
        for i,(a,b) in enumerate(packet['outer_pairs']):
            val=lambda v:env[v] if isinstance(v,str) else v
            assert val(a)-val(b)==(-1 if i==0 else 0)
        histories+=1;rows+=len(chosen)
    assert histories
    return dict(actual_U21_halted_histories=histories,chronological_rows=rows,
        scope='Positive outer packs and actual joined AND, not materialized native Pell witnesses.')


def guard_audit():
    old=parent.build();bad=[]
    for key,value in (('parameters',['wrong','input']),('minimum_half_margin',1),
                      ('table',parent.TABLE[:-1]),('form','bad')):
        bad.append(dict(old,**{key:value}))
    for name in (DELETED,PARTIAL,'initial_program_149'):
        bad.append(dict(old,source=[(n,op,b,a) if n==name else (n,op,a,b)
                                    for n,op,a,b in old['source']]))
    bad.append(build())
    for packet in bad:
        try:rewrite(packet)
        except AssertionError:pass
        else:raise AssertionError('invalid caller accepted')
    return len(bad)


def verify():
    records=[]
    for i,form in enumerate(FORMS):
        packet=build(form);ss,out=polynomial_source(packet)
        records.append(dict(form=form,ledger=ledger(packet),audit=source_audit(packet,410092+i),
            source=ss,output=out,parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],
            source_sha256=hashlib.sha256(json.dumps(ss,separators=(',',':')).encode()).hexdigest()))
    assert records[-1]['ledger']['product']['operations']==410
    assert records[-1]['ledger']['product']['multiplications']==147
    assert records[-1]['ledger']['product']['degree_upper_bound']==42589
    return dict(status='PASS_KOREC_PACKED_POSITIVE_PROGRAM410',records=records,
        symbolic_nonhalting_loops=symbolic_loops(),histories=history_audit(),
        rejected_callers=guard_audit(),
        scope='Complete U21 universal positive-program/ordinary-input relation; direct soundness at height_slack=1. Affine whole-output identity to411 may have nonpositive parent slack; no same-supplied-positive-zero-set claim.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['records'][-1]['ledger']);print(result['histories'])

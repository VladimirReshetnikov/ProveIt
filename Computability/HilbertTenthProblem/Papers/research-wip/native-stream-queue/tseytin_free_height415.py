"""Transfer the established input-language height argument to literal C2.

Supply D directly. The valid query's zero runs are at most4, whereas
B=2**16*D; typed first digits recover I<D. Terminal radix bounds follow
from the paid transports. Three additions disappear; positive acceptance
is preserved without claiming a positive inverse to the old height gap.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import tseytin_repunit_sharing418 as parent

base=parent.parent
word=base.word
execute=parent.execute
scale=parent.scale
DELETED={'height_sum__0','height_sum__1','height_sum__2'}


def rewrite(old):
    merge=old['merge_units']
    assert type(merge) is bool and old==parent.build(merge_units=merge),'full canonical418 parent required'
    rows={n:(op,a,b) for n,op,a,b in old['source']}
    required={'height_sum__0':('+','Ufinal','c2_initial'),
        'height_sum__1':('+','c2_terminal','height_sum__0'),
        'height_sum__2':('+','height_slack','height_sum__1'),
        'B__3':('*','height_sum__2',65536),
        'range_cell__274':('-','height_sum__2',1),
        'c2_terminal_product':('*',4096,'Ufinal'),
        'c2_terminal':('+','c2_terminal_product',3145)}
    assert all(rows.get(n)==v for n,v in required.items())
    for name,expected in [('height_sum__0',{'height_sum__1'}),
                          ('height_sum__1',{'height_sum__2'}),
                          ('height_sum__2',{'B__3','range_cell__274'}),
                          ('height_slack',{'height_sum__2'})]:
        assert {n for n,_,a,b in old['source'] if name in (a,b)}==expected
    alias=lambda a:'height_slack' if a=='height_sum__2' else a
    source=[(n,op,alias(a),alias(b)) for n,op,a,b in old['source'] if n not in DELETED]
    source=scale.sort_source(source,old['parameters']+old['auxiliaries'])
    scale.checked_source(source,old['parameters'],old['auxiliaries'])
    result=scale.metadata(dict(old,source=source,free_height_parent=old,free_height=True,
        interfaces=dict(old['interfaces'],height='height_slack'),
        identical_complete_polynomial=False,identical_positive_coordinates=False,
        identical_positive_zero_set=False,
        positive_zero_bijection=False,
        height_coordinate='height_slack is the positive height D, not a gap',
        height_equivalence='Accepted-input equivalence on valid program slices; exact affine integer lift, whose inverse need not be positive.'))
    before=parent.naive_degrees(old['source'],old['parameters']+old['auxiliaries'])
    after=parent.naive_degrees(source,result['parameters']+result['auxiliaries'])
    assert all(after[n]==d for n,d in before.items() if n not in DELETED)
    assert result['operations']==old['operations']-3
    assert result['multiplications']==old['multiplications']
    return result


@lru_cache(None)
def build(*,merge_units=True): return rewrite(parent.build(merge_units=merge_units))


def checked_packet(packet):
    assert packet==build(merge_units=packet['merge_units']),'complete canonical free-height packet required'


def polynomial_source(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    checked_packet(packet)
    return word.norms.polynomial_source(packet,sum_of_squares=sum_of_squares)


def degree_bound(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    checked_packet(packet)
    return parent.degree_bound(packet['free_height_parent'],sum_of_squares=sum_of_squares)


def ledger(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    source,out=polynomial_source(packet,sum_of_squares=sum_of_squares)
    c=Counter(op for _,op,_,_ in source)
    return dict(certificate={k:packet[k] for k in
        ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(source),multiplications=c['*'],
            additions_subtractions=c['+']+c['-'],output=out,
            **degree_bound(packet,sum_of_squares=sum_of_squares)))


def lift_to_parent(values):
    return dict(values,height_slack=values['height_slack']-values['c2_initial']-4097*values['Ufinal']-3145)


def project_from_parent(values):
    return dict(values,height_slack=values['height_slack']+values['c2_initial']+4097*values['Ufinal']+3145)


def assignment_audit(cases=96):
    totals=Counter();rng=random.Random(415417)
    for merge in (False,True):
        p=build(merge_units=merge);old=p['free_height_parent']
        for case in range(cases):
            signed=case>=cases//2
            draw=lambda:rng.randrange(-4,5) if signed else rng.randrange(1,5)
            values={n:draw() for n in p['parameters']+p['auxiliaries']}
            lifted=lift_to_parent(values)
            assert project_from_parent(lifted)==values
            a=execute(p['source'],values);b=execute(old['source'],lifted)
            assert all(a[n]==b[n] for n,_,_,_ in old['source'] if n not in DELETED)
            assert b['height_sum__2']==values['height_slack']
            for sos in (False,True):
                ns,no=polynomial_source(p,sum_of_squares=sos)
                os,oo=parent.polynomial_source(old,sum_of_squares=sos)
                assert execute(ns,values)[no]==execute(os,lifted)[oo]
                totals['complete_affine_output_identities']+=1
                totals['signed_output_identities']+=signed
            totals['nonpositive_algebraic_inverse_gaps']+=lifted['height_slack']<=0
            if not signed:
                projected=project_from_parent(values)
                assert min(projected.values())>0 and lift_to_parent(projected)==values
                totals['positive_parent_projections']+=1
    return dict(totals)


def max_zero_run(n):
    assert n>0
    return max(map(len,bin(n)[2:].split('1')))


def language_audit():
    # Every nonzero base-eight digit has at most two leading/trailing zeros.
    digits=[format(i,'03b') for i in range(1,7)]
    assert all(max(map(len,(a+b).split('1')))<=4 for a in digits for b in digits)
    checked=excluded=recovered=0
    for I in range(1,4096):
        if max_zero_run(I)>4:continue
        for d in range(9):
          for k in (5,6,16):
            D=1<<d;B=1<<(d+k);residue=I%B;checked+=1
            if I>=B:assert residue>=D;excluded+=1
            if residue<D:assert I==residue and I<D;recovered+=1
    # Sharp out-of-language obstruction: a wrapped residue alone is not enough.
    obstructions=[]
    for d in (1,3,8):
        D=1<<d;B=65536*D;I=B+1
        assert I%B<D and I>=B and max_zero_run(I)>4
        obstructions.append(dict(D=D,B=B,I=I))
    queries=0
    for rank in (2,4):
      for relators in ((),((1,2,-1,-2),)):
        S=base.loader.program_word(rank,relators)
        for x in range(1,17):
            I=8*base.loader.encode(base.loader.query_word(S,x))+6
            assert max_zero_run(I)<=4 and I%8==6
            queries+=1
    return dict(pairwise_digit_bound_cases=36,generic_radix_residues=checked,
        excluded_wraps=excluded,recovered_initial_bounds=recovered,
        literal_queries=queries,out_of_language_counterexamples=obstructions)


def terminal_audit():
    checked=outside_height=0
    for B in range(2,13):
      for t in (1,2,3):
        P=B**t
        for N in range(P):
          for initial in range(B):
            H,terminal=(B*N+initial)%P,(B*N+initial)//P
            if not terminal:continue
            assert terminal<B and H%B==initial
            assert H//B==N%(P//B) and terminal==N//(P//B)
            checked+=1
    maps=word._history()['maps']
    for D in (1,2,3,4,8,16):
        for a,c,b,d in maps:
          for state in range(D):
            for slope,offset in ((a,c),(b,d)):
                update=slope*state+offset
                assert 0<=update<65536*D
                outside_height+=update>=D
    return dict(exact_terminal_transport_cases=checked,
        actual_tile_updates_exceeding_current_height=outside_height)


def pretyping_audit():
    cases=0;p=build()
    for D in (1,2,3,8,16):
      for J in (1,2,3,8):
       for tile in (0,5,14,23):
        values={n:1 for n in p['parameters']+p['auxiliaries']}
        values['height_slack']=D;values[f'Shat{tile}']=J+1
        B=65536*D;P=(B-1)*J+1;values['global_bound']=P-10
        e=execute(p['source'],values)
        assert e['P__30']==P and e['global_lhs__40']==P
        assert e['range_cell__274']==D-1 and e['and__q']>=16 and e['and__F3']>=8
        T=P**34
        assert 0<=e['joined_H__286']<T
        assert 0<=e['joined_M__292']<T
        assert 0<=e['joined_Z__294']<T
        assert e['joined_H__287']//T==B
        assert e['joined_M__293']//T==B-1
        cases+=1
    return dict(positive_global_sum_contexts=cases,height_one_contexts=16,
        scope='Pretyping packed-word checks; these assignments are not full Pell or chronological zeros.')


def guards():
    old=parent.build();bad=[dict(old,source=old['source'][:-1]),
        dict(old,interfaces={'height':'height_sum__0'}),dict(old,comparisons=[]),
        dict(old,program_recipe='unrestricted'),dict(old,source=old['source']+[('leak','+','height_sum__1',1)])]
    for p in bad:
        try:rewrite(p)
        except (AssertionError,KeyError):pass
        else:raise AssertionError('mutated parent accepted')
    return len(bad)


def verify():
    records=[]
    for merge in (False,True):
      for sos in (False,True):
        p=build(merge_units=merge);source,out=polynomial_source(p,sum_of_squares=sos)
        rec=ledger(p,sum_of_squares=sos)
        assert len(source)==(415 if merge else 417)
        assert rec['polynomial']['multiplications']==194 and p['witnesses']==65
        base.baseline.closure(source,out,p['parameters']+p['auxiliaries'])
        rec.update(merge_units=merge,sum_of_squares=sos,source=source,output=out,
            parameters=p['parameters'],auxiliaries=p['auxiliaries'],comparisons=p['comparisons'],
            source_sha256=hashlib.sha256(json.dumps(source,separators=(',',':')).encode()).hexdigest())
        records.append(rec)
    return dict(status='PASS_TSEYTIN_FREE_HEIGHT415',forms=records,assignments=assignment_audit(),
        language=language_audit(),terminal=terminal_audit(),pretyping=pretyping_audit(),
        rejected_parents=guards(),scope='Established U9 bounded-zero-run and terminal-radix lemmas applied to literal C2 queries. Complete valid-program acceptance equivalence, no positive old-gap inverse or full giant Pell zero claimed.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['assignments']);print(result['language'])

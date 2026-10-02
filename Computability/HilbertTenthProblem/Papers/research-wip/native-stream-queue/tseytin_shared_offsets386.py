"""Share a paid selector prefix across common affine offsets:387 ->386.

Exact complete integer-polynomial identity on the same coordinates,
program numerals and literal24 maps. The finite min-offset search parent
is unchanged: this uses an additional common-offset decomposition.
"""
import argparse
from collections import Counter
from copy import deepcopy
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random
from math import prod

import tseytin_permuted_digits387 as parent

scale=parent.scale
DELETED='linear_coefficient__365'
PRIVATE={DELETED,'linear_sum__384','linear_sum__385','linear_sum__386',
         'linear_sum__387','linear_coefficient__367','linear_coefficient__369'}
REQUIRED={
    'selector_sum__4':('+','Shat0','Shat1'),
    **{f'selector_sum__{i}':('+',f'Shat{i-3}',f'selector_sum__{i-1}') for i in range(5,9)},
    **{f'linear_group__{362+2*i}':('+',f'Shat{6+2*i}',f'Shat{7+2*i}') for i in range(4)},
    'c2_shared_selector_sum_0':('+','selector_sum__8','linear_group__362'),
    **{f'c2_shared_selector_sum_{i}':('+',f'c2_shared_selector_sum_{i-1}',f'linear_group__{362+2*i}') for i in range(1,4)},
    'linear_sum__381':('+','Shat0','selector_sum__4'),
    'linear_sum__382':('+','linear_sum__381','selector_sum__5'),
    'linear_sum__383':('+','linear_sum__382','selector_sum__6'),
    'linear_sum__384':('+','linear_sum__383','selector_sum__7'),
    'linear_sum__385':('+','linear_group__362','linear_sum__384'),
    'linear_coefficient__365':('*','linear_group__364',2),
    'linear_sum__386':('+','linear_coefficient__365','linear_sum__385'),
    'linear_coefficient__367':('*','linear_group__366',11),
    'linear_sum__387':('+','linear_coefficient__367','linear_sum__386'),
    'linear_coefficient__369':('*','linear_group__368',19),
    'linear_sum__388':('+','linear_coefficient__369','linear_sum__387')}
CHANGES={
    'linear_sum__384':('-','linear_sum__383','Shat5'),
    'linear_sum__385':('+','c2_shared_selector_sum_3','linear_sum__384'),
    'linear_sum__386':('+','linear_group__364','linear_sum__385'),
    'linear_coefficient__367':('*','linear_group__366',10),
    'linear_coefficient__369':('*','linear_group__368',18)}
CONSUMERS={DELETED:{'linear_sum__386'},'linear_sum__384':{'linear_sum__385'},
    'linear_sum__385':{'linear_sum__386'},'linear_sum__386':{'linear_sum__387'},
    'linear_sum__387':{'linear_sum__388'},'linear_coefficient__367':{'linear_sum__387'},
    'linear_coefficient__369':{'linear_sum__388'}}


def leaves(value):
    if isinstance(value,str):return {value}
    if isinstance(value,dict):return set().union(*(leaves(k)|leaves(v) for k,v in value.items()),set())
    if isinstance(value,(tuple,list)):return set().union(*(leaves(v) for v in value),set())
    return set()


def rewrite_rows(rows,*,exported=()):
    """Guarded local identity; caller must guard its host and topologically sort.

    Exported roots include every live external interface/comparison. This
    helper does not certify an arbitrary host's universality or domains.
    """
    actual={n:(o,a,b) for n,o,a,b in rows}
    assert len(actual)==len(rows),'unique source definitions required'
    assert all(actual.get(n)==v for n,v in REQUIRED.items()),'exact prefix/common-offset rows required'
    for name,want in CONSUMERS.items():
        assert {n for n,_,a,b in rows if name in (a,b)}==want,'changed private prefix gained a consumer'
    assert not PRIVATE&leaves(exported),'changed private prefix exported'
    return [(n,*CHANGES.get(n,(o,a,b))) for n,o,a,b in rows if n!=DELETED]


def rewrite(old):
    merge=old.get('merge_units')
    assert type(merge)is bool and old==parent.build(merge_units=merge),'complete canonical387 parent required'
    active=('parameters','auxiliaries','comparisons','ordinary_comparisons','interfaces',
            'unit_register','word_unit_register','power_unit_register','word_factors','power_factors')
    source=rewrite_rows(old['source'],exported={k:old[k] for k in active})
    source=scale.sort_source(source,old['parameters']+old['auxiliaries'])
    scale.checked_source(source,old['parameters'],old['auxiliaries'])
    keys=active+('merge_units','letter_codes','tiles','program_recipe','positive_integer_domain')
    p=scale.metadata(dict({k:deepcopy(old[k]) for k in keys},source=source,
        shared_offsets_parent=old,shared_offsets=True,
        identical_complete_polynomial=True,identical_positive_zero_set=True,
        positive_zero_bijection=True,identity_reference='canonical permuted-digits387 parent on identical supplied coordinates',
        projection='Exact complete integer polynomial identity with387. Every parameter, positive domain, tile, program recipe and accepted-input slice is unchanged.'))
    assert p['operations']==old['operations']-1 and p['multiplications']==old['multiplications']-1
    assert p['additions_subtractions']==old['additions_subtractions']
    return p


@lru_cache(None)
def build(*,merge_units=True):return rewrite(parent.build(merge_units=merge_units))


def checked_packet(packet):
    assert packet==build(merge_units=packet['merge_units']),'complete canonical shared-offset386 packet required'


def polynomial_source(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    checked_packet(packet)
    return parent.literal.norms.polynomial_source(packet,sum_of_squares=sum_of_squares)


def degree_dictionary(packet):
    checked_packet(packet)
    return parent.parent.degree_helper.degree_dictionary(dict(packet,word_strong_normalized=True))


def degree_bound(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    source,out=polynomial_source(packet,sum_of_squares=sum_of_squares)
    degrees=degree_dictionary(packet);d=lambda v:degrees[v] if isinstance(v,str) else 0
    for n,o,a,b in source:
        if n not in degrees:degrees[n]=d(a)+d(b) if o=='*' else max(d(a),d(b))
    return dict(degree_upper_bound=degrees[out],word_factor_degree_bounds=[d(n) for n in packet['word_factors']],
        power_factor_degrees=[d(n) for n in packet['power_factors']],
        maximum_ordinary_residual_degree=max(max(d(a),d(b)) for a,b in packet['ordinary_comparisons']),exact_degree_claimed=False)


def ledger(packet=None,*,sum_of_squares=False):
    if packet is None:packet=build()
    rows,out=polynomial_source(packet,sum_of_squares=sum_of_squares);c=Counter(o for _,o,_,_ in rows)
    return dict(certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(rows),multiplications=c['*'],additions_subtractions=c['+']+c['-'],output=out,
                        **degree_bound(packet,sum_of_squares=sum_of_squares)))


def execute(rows,values):
    e=dict(values)
    at=lambda v:e[v] if isinstance(v,str) else v
    for n,o,a,b in rows:e[n]=at(a)*at(b) if o=='*' else at(a)+at(b) if o=='+' else at(a)-at(b)
    return e


def restore_private(e):
    h=[e[f'Shat{i}'] for i in range(14)];W=sum((5-i)*h[i] for i in range(6))
    A,B,C,D=[h[i]+h[i+1] for i in (6,8,10,12)]
    return dict(e,linear_sum__384=W,linear_sum__385=W+A,linear_sum__386=W+A+2*B,
        linear_sum__387=W+A+2*B+11*C,linear_coefficient__365=2*B,
        linear_coefficient__367=11*C,linear_coefficient__369=19*D)


def source_audit(cases=96):
    rng=random.Random(386387);counts=Counter()
    for merge in (False,True):
        p=build(merge_units=merge);old=p['shared_offsets_parent']
        for case in range(cases):
            signed=case>=cases//2;draw=lambda:rng.randrange(-5,6) if signed else rng.randrange(1,5)
            values={n:draw() for n in p['parameters']+p['auxiliaries']}
            if case%16==0:values.update({f'Shat{i}':1 for i in range(24)});counts['zero_decoded_selector_cases']+=1
            e=execute(p['source'],values);past=execute(old['source'],values);restored=restore_private(e)
            assert all(restored[n]==past[n] for n,_,_,_ in old['source'])
            assert e['linear_sum__388']==past['linear_sum__388']
            counts['complete_private_restore_register_maps']+=1;counts['signed_register_maps']+=signed
            for sos in (False,True):
                rows,out=polynomial_source(p,sum_of_squares=sos);other,target=parent.polynomial_source(old,sum_of_squares=sos)
                env=execute(rows,values);assert env[out]==execute(other,values)[target]
                at=lambda n:env[n] if isinstance(n,str) else n
                ordinary=sum((at(a)-at(b))**2 for a,b in p['ordinary_comparisons'])
                W=prod(env[n] for n in p['word_factors']);P=prod(env[n] for n in p['power_factors'])
                manual=(W*P-1)**2+ordinary if merge and sos else W*P*(1+ordinary)-1 if merge else (W-1)**2+(P-1)**2+ordinary if sos else W*(1+ordinary+(P-1)**2)-1
                assert env[out]==manual
                counts['complete_parent_and_manual_outputs']+=1;counts['signed_outputs']+=signed
    return dict(counts)


def exact_linear_audit():
    import sympy as sp
    h=sp.symbols('h0:14');C=sum(h[:6]);pairs=[sum(h[i:i+2]) for i in (6,8,10,12)];A,B,E,F=pairs
    W=sum((5-i)*h[i] for i in range(6));P=C+A+B+E+F
    newcopy=h[0]+sum(h[:2])+sum(h[:3])+sum(h[:4])-h[5]
    assert sp.expand(newcopy-(W-C))==0
    assert sp.expand(newcopy+P+B+10*E+18*F-(W+A+2*B+11*E+19*F))==0
    return dict(exact_linear_identities=2,scope='All integer selector hats, without one-hot, nonnegativity or history hypotheses.')


def guards():
    old=parent.build();count=0
    def reject(call):
        nonlocal count
        try:call()
        except (AssertionError,KeyError):count+=1
        else:raise AssertionError('malformed caller accepted')
    for name in REQUIRED:
        bad=[(n,o,a,17 if n==name else b) for n,o,a,b in old['source']]
        reject(lambda bad=bad:rewrite_rows(bad))
    for name in PRIVATE:
        reject(lambda name=name:rewrite_rows(old['source']+[('extra_consumer','+',name,1)]))
        reject(lambda name=name:rewrite_rows(old['source'],exported={'nested':[None,{'port':(name,)}]}))
    reject(lambda:rewrite_rows(old['source']+[old['source'][0]]))
    for key,val in [('interfaces',{}),('auxiliaries',[]),('program_recipe','new'),('letter_codes',{})]:
        reject(lambda key=key,val=val:rewrite(dict(old,**{key:val})))
    packet=build()
    for key,val in [('source',packet['source'][:-1]),('identity_reference','unrelated'),('comparisons',[])]:
        for api in (polynomial_source,degree_bound):reject(lambda key=key,val=val,api=api:api(dict(packet,**{key:val})))
    return count


def verify():
    forms=[]
    for merge in (False,True):
        p=build(merge_units=merge);old=p['shared_offsets_parent']
        before=parent.degree_dictionary(old);after=degree_dictionary(p)
        assert set(after)==set(before)-{DELETED} and all(after[n]==before[n] for n in after)
        for sos in (False,True):
            rows,out=polynomial_source(p,sum_of_squares=sos);record=ledger(p,sum_of_squares=sos)
            # Full output reachability, including each rebuilt private prefix.
            lookup={n:(a,b) for n,_,a,b in rows};seen=set();todo=[out]
            while todo:
                n=todo.pop()
                if isinstance(n,str) and n in lookup and n not in seen:seen.add(n);todo.extend(lookup[n])
            assert seen==lookup.keys()
            assert record['polynomial']['operations']==(386 if merge else 388)
            assert record['polynomial']['multiplications']==178
            assert record['polynomial']['additions_subtractions']==(208 if merge else 210)
            assert degree_bound(p,sum_of_squares=sos)==parent.degree_bound(old,sum_of_squares=sos)
            record.update(merge_units=merge,sum_of_squares=sos,source=rows,output=out,
                parameters=p['parameters'],auxiliaries=p['auxiliaries'],comparisons=p['comparisons'],
                retained_degree_dictionary_entries=len(after),source_sha256=hashlib.sha256(json.dumps(rows,separators=(',',':')).encode()).hexdigest())
            forms.append(record)
    return dict(status='PASS_TSEYTIN_SHARED_OFFSETS386',forms=forms,identities=exact_linear_audit(),
        source_audit=source_audit(),rejected_callers=guards(),
        scope='Exact complete integer-polynomial identity with canonical387 and identical domains/program recipe; no new semantic encoding or a broader circuit-optimum claim.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['source_audit'])

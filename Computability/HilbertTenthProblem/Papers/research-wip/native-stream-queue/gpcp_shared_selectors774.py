"""Share paid selector sums in the complete ordered U15,2 compiler.

Exactly31 additions disappear from either canonical normalized initial
interface. Complete integer polynomials, domains and program recipes agree.
This is a fixed cover, not an arithmetic-circuit optimality claim.
"""
import argparse
from collections import Counter
from copy import deepcopy
from functools import lru_cache
import hashlib
import json
from math import prod
from pathlib import Path
import random

import gpcp_normalized_strong_compiler as parent

PREFIX='hist__selector_sum__'
ROOT=PREFIX+'59'
FIRST=PREFIX+'4'
OLD_PREFIX={PREFIX+str(i) for i in range(4,60)}
ERASED=OLD_PREFIX-{FIRST,ROOT}
# These are existing scalar registers, not new free summation gates.
COVER=(
 ('hist__Shat2',(2,)),('hist__Shat3',(3,)),
 ('hist__Shat31',(31,)),('hist__Shat32',(32,)),
 ('hist__Shat37',(37,)),('hist__Shat46',(46,)),
 ('hist__Shat50',(50,)),('hist__Shat52',(52,)),
 (FIRST,(0,1)),('hist__group_sum__457',(4,5)),
 ('hist__group_sum__472',tuple(range(6,21))),
 ('hist__group_sum__482',(21,22,23,24,29)),
 ('hist__Shat48',(48,)),('hist__Shat56',(56,)),
 ('hist__linear_group__617',(25,26,27,28)),
 ('hist__linear_group__619',(30,39)),
 ('hist__linear_group__621',(34,36)),
 ('hist__linear_group__698',(33,35)),
 ('hist__linear_group__626',(40,41)),
 ('hist__linear_group__707',(42,53)),
 ('hist__linear_group__709',(43,54)),
 ('hist__linear_group__623',(38,47)),
 ('hist__Shat49',(49,)),('hist__linear_group__716',(51,55)),
 ('hist__linear_group__628',(44,45)))
ACTIVE=('parameters','auxiliaries','comparisons','unit_factors','unit_register',
 'native_prefixes','width','inline_initial','program_code','machine',
 'binary_prefix_code','block_words','block_values','terminal_word','terminal_bits',
 'orientation_mode','rule_order','code_variant','loaded_input','loader_operations',
 'regroup','unit_product','tiles','layout')


def leaves(value):
    if isinstance(value,str):return {value}
    if isinstance(value,dict):return set().union(*(leaves(k)|leaves(v) for k,v in value.items()),set())
    if isinstance(value,(list,tuple)):return set().union(*(leaves(v) for v in value),set())
    return set()


def cover_audit(old):
    """Expand the actual paid definitions as exact integer coefficient vectors."""
    rows=old['source'];nodes={n:(o,a,b) for n,o,a,b in rows}
    assert len(nodes)==len(rows)
    assert nodes[FIRST]==('+','hist__Shat0','hist__Shat1')
    for i in range(5,60):assert nodes[PREFIX+str(i)]==('+',f'hist__Shat{i-3}',PREFIX+str(i-1))
    assert nodes['hist__J__60']==('-',ROOT,57)
    for i in range(5,59):
        name=PREFIX+str(i)
        assert {n for n,_,a,b in rows if name in (a,b)}=={PREFIX+str(i+1)}
    assert not ERASED&leaves({k:old[k] for k in ACTIVE})
    hats={f'hist__Shat{i}':i for i in range(57)};cone=set()
    @lru_cache(None)
    def vector(name):
        if name in hats:return tuple(int(j==hats[name]) for j in range(57))
        assert name not in OLD_PREFIX-{FIRST},'cover depends on erased prefix or J'
        op,a,b=nodes[name];assert op=='+','cover must consist of literal paid additions'
        cone.add(name);return tuple(x+y for x,y in zip(vector(a),vector(b)))
    combined=[0]*57
    for name,support in COVER:
        actual=vector(name);want=tuple(int(j in support) for j in range(57))
        assert actual==want
        combined=[a+b for a,b in zip(combined,actual)]
    assert combined==[1]*57 and len(COVER)==25
    return dict(blocks=[dict(register=n,indices=list(s)) for n,s in COVER],
                cover_definition_rows=[row for row in rows if row[0] in cone],
                disjoint=True,covered_selectors=57,paid_blocks=25,
                original_prefix_additions=56,retained_first_addition=1,
                new_join_additions=24,saved_additions=31)


def sorted_source(rows,inputs):
    available=set(inputs);pending=list(rows);result=[]
    assert len({r[0] for r in rows})==len(rows)
    while pending:
        ready=[r for r in pending if all(type(a)is int or a in available for a in r[2:])]
        assert ready,'cycle or unknown input'
        for row in ready:
            assert row[0] not in available
            result.append(row);available.add(row[0])
        done={r[0] for r in ready};pending=[r for r in pending if r[0] not in done]
    return result


@lru_cache(None)
def canonical(inline_initial):
    assert type(inline_initial)is bool
    return parent.build_ordered_universal(inline_initial=inline_initial)


def rewrite(old):
    inline=old.get('inline_initial')
    assert type(inline)is bool and old==canonical(inline),'complete canonical normalized ordered U15,2 parent required'
    audit=cover_audit(old)
    rows=[r for r in old['source'] if r[0] not in OLD_PREFIX-{FIRST}]
    acc=COVER[0][0]
    for i,(term,_) in enumerate(COVER[1:]):
        name=ROOT if i==23 else f'shared_selector_join_{i}'
        rows.append((name,'+',acc,term));acc=name
    rows=sorted_source(rows,old['parameters']+old['auxiliaries'])
    counts=Counter('M' if o=='*' else 'A' for _,o,_,_ in rows)
    p={k:deepcopy(old[k]) for k in ACTIVE}
    # All nested parent emitters/coordinate stages are historical provenance.
    # Active history geometry stores data only; the emitted source is rows.
    geometry=('maps','layout','tiles','K','baselines','groups_U','groups_V','selected_products','scale_exponent','region_exponents')
    p.update(source=rows,operations=len(rows),multiplications=counts['M'],
        additions_subtractions=counts['A'],equations=len(p['comparisons']),witnesses=len(p['auxiliaries']),
        history_packet={k:deepcopy(old['history_packet'][k]) for k in geometry},
        selector_sharing_parent=old,selector_cover=audit,shared_selectors=True,
        identical_complete_integer_polynomial=True,identical_positive_zero_set=True,
        positive_zero_bijection='identity on every supplied coordinate, before valid-program restriction',
        projection='Same complete normalized ordered U15,2 polynomial, program data, positive domains and ordinary input; only paid selector-sum reuse.')
    assert len(rows)==old['operations']-31 and counts['M']==old['multiplications']
    assert counts['A']==old['additions_subtractions']-31
    return p


@lru_cache(None)
def build(*,inline_initial=True):return rewrite(canonical(inline_initial))


def checked(packet):
    inline=packet.get('inline_initial')
    assert type(inline)is bool and packet==build(inline_initial=inline),'complete canonical shared-selector packet required'


def polynomial_source(packet=None):
    if packet is None:packet=build()
    checked(packet);return parent.polynomial_source(packet)


def raw_degrees(packet):
    """Literal propagation with three fully guarded expanded main norms."""
    rows={n:(o,a,b) for n,o,a,b in packet['source']}
    degrees={n:1 for n in packet['parameters']+packet['auxiliaries']}
    at=lambda n:degrees[n] if isinstance(n,str) else 0
    for n,o,a,b in packet['source']:
        degrees[n]=at(a)+at(b) if o=='*' else max(at(a),at(b))
        for prefix in parent.PREFIXES:
            if n!=prefix+'R15':continue
            X,ac,G,aa,cc,H=[prefix+x for x in ('wn2','cam2','gam','R12','R10a','a4m5')]
            expected={prefix+'R15':('-',prefix+'L15',prefix+'Ac2'),prefix+'R14':('+',prefix+'D1',G),
                prefix+'D1':('+',X,ac),ac:('*',cc,aa),G:('*',prefix+'ga',H),
                H:('+',prefix+'a4',3),prefix+'a4':('*',4,aa),
                prefix+'A':('+',prefix+'a_square',H),prefix+'a_square':('*',aa,aa),
                prefix+'c2':('*',cc,cc),prefix+'Ac2':('*',prefix+'A',prefix+'c2'),
                prefix+'L15':('*',prefix+'R14',prefix+'R14')}
            assert all(rows[k]==v for k,v in expected.items())
            degrees[n]=max(2*at(X),at(X)+at(ac),at(X)+at(G),at(ac)+at(G),2*at(G),at(H)+2*at(cc))
    return degrees


def degree_dictionary(packet=None):
    if packet is None:packet=build()
    checked(packet);return raw_degrees(packet)


def degree_audit(packet=None):
    if packet is None:packet=build()
    checked(packet)
    exact=parent.degree_audit(packet)
    assert exact==parent.degree_audit(packet['selector_sharing_parent'])
    return exact


def ledger(packet=None):
    if packet is None:packet=build()
    rows,out=polynomial_source(packet);counts=Counter('M' if o=='*' else 'A' for _,o,_,_ in rows)
    return dict(certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(rows),multiplications=counts['M'],additions_subtractions=counts['A'],output=out),
        degree=degree_audit(packet),parameters=packet['parameters'],inline_initial=packet['inline_initial'])


def execute(rows,values):
    e=dict(values)
    for n,o,a,b in rows:
        a=e[a] if isinstance(a,str) else a;b=e[b] if isinstance(b,str) else b
        e[n]=a*b if o=='*' else a+b if o=='+' else a-b
    return e


def restore_prefixes(env):
    out=dict(env);total=env['hist__Shat0']
    for i in range(1,57):
        total+=env[f'hist__Shat{i}'];out[PREFIX+str(i+3)]=total
    return out


def source_audit(cases=64):
    rng=random.Random(77457);counts=Counter()
    for inline in (False,True):
        p=build(inline_initial=inline);old=p['selector_sharing_parent']
        rows,out=polynomial_source(p);before,target=parent.polynomial_source(old)
        for case in range(cases):
            signed=case>=cases//2
            v={n:rng.randrange(-3,4) if signed else rng.randrange(1,5) for n in p['parameters']+p['auxiliaries']}
            if case%16==0:v.update({f'hist__Shat{i}':1 for i in range(57)});counts['zero_decoded_selector_cases']+=1
            env=execute(rows,v);past=execute(before,v);lift=restore_prefixes(env)
            assert all(lift[n]==past[n] for n,_,_,_ in old['source'])
            at=lambda a:env[a] if isinstance(a,str) else a
            residuals=[at(a)-at(b) for a,b in p['comparisons'][:-1]]
            manual=prod(env[n] for n in p['unit_factors'])*(1+sum(r*r for r in residuals))-1
            assert env[out]==past[target]==manual
            counts['complete_register_prefix_restorations']+=1;counts['complete_parent_manual_outputs']+=1
            counts['signed_maps']+=signed
    return dict(counts)


def rejection_audit():
    old=canonical(True);count=0
    def reject(f):
        nonlocal count
        try:f()
        except (AssertionError,KeyError):count+=1
        else:raise AssertionError('malformed caller accepted')
    for key,value in [('source',old['source'][:-1]),('parameters',[]),('auxiliaries',[]),
                      ('comparisons',[]),('machine',{}),('binary_prefix_code',{})]:
        reject(lambda key=key,value=value:rewrite(dict(old,**{key:value})))
    p=build()
    for key,value in [('source',p['source'][:-1]),('comparisons',[]),('parameters',[]),('projection','wrong')]:
        for api in (polynomial_source,degree_dictionary,degree_audit,ledger):
            reject(lambda key=key,value=value,api=api:api(dict(p,**{key:value})))
    for name in ERASED:
        reject(lambda name=name:cover_audit(dict(old,source=old['source']+[('extra_consumer','+',name,1)])))
    reject(lambda:cover_audit(dict(old,comparisons=old['comparisons']+[(PREFIX+'12',1)])))
    for name,_ in COVER:
        if name.startswith('hist__Shat'):continue
        changed=[(n,o,a,987654 if n==name else b) for n,o,a,b in old['source']]
        reject(lambda changed=changed:cover_audit(dict(old,source=changed)))
    return count


def verify():
    forms=[]
    for inline in (False,True):
        p=build(inline_initial=inline);old=p['selector_sharing_parent'];rows,out=polynomial_source(p)
        rec=ledger(p);assert rec['polynomial']['operations']==(774 if inline else 777)
        assert rec['polynomial']['multiplications']==(352 if inline else 353)
        assert rec['polynomial']['additions_subtractions']==(422 if inline else 424)
        assert rec['degree']['exact_degree']==(205092 if inline else 8532)
        d=raw_degrees(p);prior=raw_degrees(old)
        assert set(prior)-set(d)==ERASED and all(d[n]==prior[n] for n in d.keys()&prior.keys())
        assert all(d[n]==1 for n in d.keys()-prior.keys())
        lookup={n:(a,b) for n,_,a,b in rows};seen=set();todo=[out]
        while todo:
            n=todo.pop()
            if isinstance(n,str) and n in lookup and n not in seen:seen.add(n);todo.extend(lookup[n])
        assert seen==lookup.keys()
        rec.update(source=rows,comparisons=p['comparisons'],auxiliaries=p['auxiliaries'],
            source_sha256=hashlib.sha256(json.dumps(rows,separators=(',',':')).encode()).hexdigest(),
            same_retained_degree_entries=len(set(d)&set(prior)),new_linear_join_rows=len(set(d)-set(prior)))
        forms.append(rec)
    return dict(status='PASS_GPCP_SHARED_SELECTORS774',forms=forms,cover=cover_audit(canonical(True)),
        identities=source_audit(),rejected_callers=rejection_audit(),
        scope='Exact complete integer polynomial and positive-domain identity on the two canonical normalized ordered U15,2 input interfaces. No circuit optimum or new universal-machine claim.')


if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--write',action='store_true');args=ap.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['identities'])
    for r in result['forms']:print(r['inline_initial'],r['polynomial'],r['degree']['exact_degree'])

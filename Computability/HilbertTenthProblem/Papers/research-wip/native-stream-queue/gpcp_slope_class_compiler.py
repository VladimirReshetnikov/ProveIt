"""Complete GPCP compilation with paid slope classes and factored transports.

Enumerate actual baseline schedules, retain the per-tile compiler as a
fallback, and compose the chosen complete raw history with the ordinary
input boundary before applying native-unit projections.
"""
import argparse
import json
from pathlib import Path
import random

import gpcp_complete_fixed_program as parent
import gpcp_complete_fixed_program_units as units
import pcp_uniform_affine_pair_history as per_tile
import pcp_affine_slope_class_history as classes
import pcp_affine_factored_transports as factored

execute=parent.execute
scalar=parent.scalar


def history_ledger(packet):
    return dict(kind=packet['history_kind'],operations=packet['operations'],
        multiplications=packet['multiplications'],additions_subtractions=packet['additions_subtractions'],
        witnesses=packet['witnesses'],selected_products=packet.get('selected_products',2*packet['tiles']),
        scale_exponent=packet['scale_exponent'],layout=packet['layout'],
        baselines=packet.get('baselines'),linear_mode=packet.get('linear_mode','literal'))


def choose_history(maps,*,factor=True,choice='auto'):
    assert choice in ('auto','slope_classes','per_tile')
    candidates=[]
    if choice in ('auto','slope_classes'):
        for a in sorted({row[0] for row in maps}):
          for b in sorted({row[2] for row in maps}):
            p=classes.build_raw(maps,baseline_U=a,baseline_V=b)
            if factor:p=factored.rewrite(p)
            candidates.append(dict(p,history_kind='slope_classes'))
    if choice in ('auto','per_tile'):
        for layout in ('contiguous','interleaved'):
            p=per_tile.build(maps,layout)
            if factor:p=factored.rewrite(p)
            candidates.append(dict(p,history_kind='per_tile'))
    best=min(candidates,key=lambda p:(p['operations'],p['witnesses'],
                                      p['scale_exponent'],p['multiplications']))
    return dict(best,history_candidates=[history_ledger(p) for p in candidates])


def rewrite(old,*,unit_product=True,regroup=True,factor=True,history_choice='auto'):
    h=choose_history(old['history_packet']['maps'],factor=factor,choice=history_choice)
    raw=factored.replace_history(old,h)
    p=units.rewrite(raw,regroup=regroup) if unit_product else raw
    return dict(p,unit_product=unit_product,factored_transports=factor,
                history_choice=history_choice,history_kind=h['history_kind'])


def build(*args,unit_product=True,regroup=True,factor=True,history_choice='auto',**kwargs):
    return rewrite(parent.build(*args,**kwargs),unit_product=unit_product,
                   regroup=regroup,factor=factor,history_choice=history_choice)


def build_for_tm(*args,unit_product=True,regroup=True,factor=True,history_choice='auto',**kwargs):
    return rewrite(parent.build_for_tm(*args,**kwargs),unit_product=unit_product,
                   regroup=regroup,factor=factor,history_choice=history_choice)


def odd_machine(*,unit_product=True,regroup=True,factor=True,history_choice='auto',**kwargs):
    return rewrite(parent.odd_machine(**kwargs),unit_product=unit_product,
                   regroup=regroup,factor=factor,history_choice=history_choice)


def polynomial_source(packet):
    return units.polynomial_source(packet) if packet['unit_product'] else parent.polynomial_source(packet)


def ledger(packet):
    result=(units.ledger(packet) if packet['unit_product'] else parent.ledger(packet))
    result.update(unit_product=packet['unit_product'],history_kind=packet['history_kind'],
        factored_transports=packet['factored_transports'],history=history_ledger(packet['history_packet']))
    result['degree_audit']=(units.degree_audit(packet) if packet['unit_product'] else parent.degree_check(packet))
    return result


def independent_raw(packet,values):
    left,right=parent.component_values(packet,values)
    rr=parent.boundary.independent(packet['boundary_packet'],left)
    if packet['inline_initial']:
        assert rr[-2]==0
        rr=rr[:-2]+rr[-1:]
    h=packet['history_packet']
    manual=classes.manual if h['history_kind']=='slope_classes' else per_tile.manual
    return rr+manual(h,right)[0]


def outer_fixture(packet,x,padding=0,code=1):
    raw=packet['raw_packet'] if packet['unit_product'] else packet
    machine=raw['machine'];width=raw['width'];pc=raw['program_code']
    loaded=x if pc is None else (code if pc=='parameter' else pc)*(2*x+1)
    n=max(2,loaded.bit_length()+padding)
    initial=('[',machine['start'])+tuple(bin(loaded)[2:].zfill(n))+(']',)
    target=('[',machine['accept'],']');word=initial;steps=[]
    for _ in range(4*n+16):
        if word==target:break
        choices=parent.boundary.successors(word,machine['rules'])
        if not choices:break
        steps.append(choices[0]);word=steps[-1][2]
    selection=parent.boundary.derivation_selection(initial,steps,machine['alphabet'],machine['rules'])
    top,bottom=parent.boundary.selected_images(machine['tiles'],selection)
    assert top+('#',)+word==initial+('#',)+bottom
    codes=machine['codes'];loaded_word=parent.boundary.code(tuple(codes[c] for c in initial+('#',)),width)
    h=raw['history_packet']
    fixture=classes.positive_outer_fixture if h['history_kind']=='slope_classes' else per_tile.positive_outer_fixture
    hv=fixture(h,selection,loaded_word)
    values={name:1 for name in raw['parameters']+raw['auxiliaries']}
    values.update(parent.boundary.outer_fixture(loaded,n,width))
    values.update(x=x,Ufinal=hv['Ufinal'],Vfinal=hv['Vfinal'])
    if pc=='parameter':values['program_code']=code
    if not raw['inline_initial']:values['Vinitial']=loaded_word
    values.update({'hist__'+name:hv[name] for name in h['auxiliaries']})
    assert all(values[name]>0 for name in raw['parameters']+raw['auxiliaries'])
    if packet['unit_product']:
        values={name:values.get(name,1) for name in packet['parameters']+packet['auxiliaries']}
        restored=units.lift(packet,values)
    else:restored=values
    env=execute(raw['source'],restored)
    assert env['input_bottom']==loaded_word
    assert all(scalar(a,env)==scalar(b,env) for a,b in raw['comparisons'][:5])
    split=raw['boundary_comparisons']
    assert all(scalar(a,env)==scalar(b,env) for a,b in raw['comparisons'][split:split+3])
    a,b=raw['comparisons'][split-1];accepts=scalar(a,env)==scalar(b,env)
    assert accepts==(word==target)==bool(loaded&1)
    assert parent.boundary.dense_append(machine['tiles'],selection,codes,width,(1,loaded_word,1))==[
        hv['Ufinal'],hv['Vfinal'],1]
    return dict(input=x,loaded_input=loaded,padding=padding,recoder_duration=n,
        history_duration=len(selection),accepted=accepts,unit_product=packet['unit_product'],
        history_kind=h['history_kind'],full_native_Pell_witnesses_materialized=False)


def verify():
    rng=random.Random(60343);rawcases=unitcases=0;records=[]
    tables=[(((0,),(1,)),),(((0,),(0,)),((1,),(1,))),
            (((0,),(1,1)),((1,0),(1,)),((1,),(0,1)))]
    for tiles in tables:
      for width in (4,9):
       for inline in (False,True):
        for pc in (None,'parameter',3):
            old=parent.build(tiles,width,(2,3),(4,5),(5,2,6,4),inline_initial=inline,program_code=pc)
            raw=rewrite(old,unit_product=False);unit=rewrite(old)
            assert raw['history_packet']['operations']<=factored.rewrite(old['history_packet'])['operations']
            for i in range(12):
                values={n:rng.randrange(1,5) if i<6 else rng.randrange(-2,4)
                        for n in raw['parameters']+raw['auxiliaries']}
                source,out=polynomial_source(raw);env=execute(source,values);rr=independent_raw(raw,values)
                assert rr==[scalar(a,env)-scalar(b,env) for a,b in raw['comparisons']]
                assert env[out]==sum(r*r for r in rr);rawcases+=1
                values={n:rng.randrange(1,5) if i<6 else rng.randrange(-2,4)
                        for n in unit['parameters']+unit['auxiliaries']}
                units.audit_identity(unit,values);unitcases+=1
            records += [ledger(raw),ledger(unit)]
    samples=[];outer=[]
    for inline in (False,True):
      for factor in (False,True):
       for unit in (False,True):
        packet=odd_machine(inline_initial=inline,factor=factor,unit_product=unit)
        samples.append(ledger(packet))
        for x in (1,2,3):outer.append(outer_fixture(packet,x,int(x==1)))
    for pc,code in (('parameter',3),('parameter',4),(8,1)):
        packet=odd_machine(program_code=pc)
        outer.append(outer_fixture(packet,1,0,code))
    for choice in ('per_tile','slope_classes'):
        packet=odd_machine(history_choice=choice)
        assert packet['history_kind']==choice
        samples.append(ledger(packet))
    example=odd_machine()
    return dict(status='PASS_GPCP_SLOPE_CLASS_COMPILER',raw_complete_identities=rawcases,
        unit_complete_identities=unitcases,half_assignments_signed=True,variant_ledgers=records,
        sample_ledgers=samples,genuine_outer_runs=outer,
        candidate_ledgers=example['history_packet']['history_candidates'],
        example=dict(ledger=ledger(example),source=example['source'],comparisons=example['comparisons'],
            parameters=example['parameters'],auxiliaries=example['auxiliaries']),
        scope='Complete ordinary-input fixed-program representation, with all paid history candidates retaining the same table. The illustrative odd-integer table is not universal. Program loader and abstract fixed-interpreter universality are inherited; no universal75/88 improvement is claimed.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])

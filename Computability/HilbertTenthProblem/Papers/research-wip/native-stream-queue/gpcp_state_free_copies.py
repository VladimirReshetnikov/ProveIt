"""Fixed-TM compilation with state-free copied contexts.

Retain the full alphabet, codes, rules and ordinary-input framing, but copy
only tape symbols and delimiters.  Equivalence is for well-formed starts
with distinct initial/accepting states, not arbitrary boundary tuples.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import gpcp_complete_fixed_program as parent
import gpcp_slope_class_compiler as slope

execute=parent.execute
scalar=parent.scalar
boundary=parent.boundary


def build_for_tm(tape,transitions,start,accept,*,width=None,unit_product=True,
                 regroup=True,factor=True,history_choice='auto',**options):
    """Same fixed-TM input/loader API, with fewer copy tiles before packing."""
    full=parent.build_for_tm(tape,transitions,start,accept,width=width,**options)
    machine=full['machine'];alphabet=machine['alphabet'];codes=machine['codes']
    copy_alphabet=tuple(c for c in alphabet if c in set(tape)|{'[',']','#'})
    states=set(alphabet)-set(copy_alphabet)
    assert start in states and accept in states and start!=accept
    assert all(sum(c in states for c in a)==sum(c in states for c in b)==1
               for a,b in machine['rules'])
    tiles=boundary.tiles_for(copy_alphabet,machine['rules'])
    embedding=[alphabet.index(c) for c in copy_alphabet]
    embedding+=list(range(len(alphabet),len(machine['tiles'])))
    assert tuple(machine['tiles'][i] for i in embedding)==tiles
    numeric=tuple(tuple(tuple(codes[c] for c in word) for word in tile) for tile in tiles)
    left=full['boundary_packet']
    raw=parent.build(numeric,full['width'],left['prefix'],left['suffix'],left['terminal'],**options)
    assert raw['boundary_packet']==full['boundary_packet']
    assert raw['source'][:full['loader_operations']+left['operations']]==full['source'][:full['loader_operations']+left['operations']]
    raw['machine']=dict(machine,tiles=tiles,copy_alphabet=copy_alphabet,
                        full_tiles=machine['tiles'],tile_embedding=embedding,
                        states=tuple(sorted(states)),transitions=dict(transitions))
    raw.update(state_free_copies=True,deleted_copy_tiles=len(states),
               full_tile_count=len(machine['tiles']))
    return slope.rewrite(raw,unit_product=unit_product,regroup=regroup,
                         factor=factor,history_choice=history_choice)


def sample_machine(name='odd'):
    tape=('0','1','_')
    if name in ('odd','even'):
        t={(s,c):(('scan' if c=='0' else 'odd'),c,'R')
           for s in ('scan','odd') for c in ('0','1')}
        t.update({('scan','_'):(('reject' if name=='odd' else 'halt'),'_','S'),
                  ('odd','_'):(('halt' if name=='odd' else 'reject'),'_','S')})
        return tape,t,'scan','halt'
    if name=='return_left':
        t={('scan',c):('scan',c,'R') for c in ('0','1')}
        t.update({('back',c):('back',c,'L') for c in ('0','1')})
        t.update({('scan','_'):('back','_','L'),('back','_'):('halt','_','S')})
        return tape,t,'scan','halt'
    assert name=='all'
    t={('scan',c):('scan',c,'R') for c in ('0','1')}
    t['scan','_']=('halt','_','S')
    return tape,t,'scan','halt'


def odd_machine(**options):
    # Keep the historical names/codes exactly, including its start symbol.
    t={(s,c):(('start' if c=='0' else 'odd'),c,'R')
       for s in ('start','odd') for c in ('0','1')}
    t.update({('start','_'):('reject','_','S'),('odd','_'):('halt','_','S')})
    return build_for_tm(('0','1','_'),t,'start','halt',**options)


def derivation_selection(machine,initial,steps):
    assert steps,'A state-free copy table cannot copy a whole unchanged configuration.'
    selection=boundary.derivation_selection(initial,steps,machine['copy_alphabet'],machine['rules'])
    top,bottom=boundary.selected_images(machine['tiles'],selection)
    oldtop,oldbottom=boundary.selected_images(machine['full_tiles'],[machine['tile_embedding'][i] for i in selection])
    assert (top,bottom)==(oldtop,oldbottom)
    assert top+('#',)+steps[-1][2]==initial+('#',)+bottom
    return selection


def polynomial_source(packet):return slope.polynomial_source(packet)


def ledger(packet):
    out=slope.ledger(packet)
    out.update(deleted_copy_tiles=packet['deleted_copy_tiles'],full_tile_count=packet['full_tile_count'])
    return out


def local_derivations(machine):
    """Check every actual rule, and complete cleanup with both contexts."""
    count=0;states=set(machine['states']);rules=machine['rules']
    for ri,(left,right) in enumerate(rules):
        for before,after in (((),()),(('0',),('1',)),(('1','0'),('0','1'))):
            prefix=() if left[0]=='[' else ('[',)+before
            suffix=() if left[-1]==']' else after+(']',)
            initial=prefix+left+suffix;target=prefix+right+suffix
            assert sum(c in states for c in initial)==sum(c in states for c in target)==1
            step=(ri,len(prefix),target)
            assert step in boundary.successors(initial,rules)
            derivation_selection(machine,initial,[step]);count+=1
    for a in ('','0','10','_01'):
      for b in ('','1','01','10_'):
        if not a+b:continue
        initial=('[',)+tuple(a)+(machine['accept'],)+tuple(b)+(']',)
        word=initial;steps=[]
        while word!=('[',machine['accept'],']'):
            choices=boundary.successors(word,rules);assert choices
            steps.append(choices[0]);word=steps[-1][2]
        assert len(steps)==len(a+b)
        derivation_selection(machine,initial,steps);count+=1
    return count


def outer_fixture(packet,x,padding=0,code=1,expected=None):
    raw=packet['raw_packet'] if packet['unit_product'] else packet
    machine=raw['machine'];pc=raw['program_code'];width=raw['width']
    loaded=x if pc is None else (code if pc=='parameter' else pc)*(2*x+1)
    n=max(2,loaded.bit_length()+padding)
    initial=('[',machine['start'])+tuple(bin(loaded)[2:].zfill(n))+(']',)
    target=('[',machine['accept'],']');word=initial;steps=[]
    for _ in range(12*n+32):
        if word==target:break
        choices=boundary.successors(word,machine['rules'])
        if not choices:break
        steps.append(choices[0]);word=steps[-1][2]
    selection=derivation_selection(machine,initial,steps)
    codes=machine['codes'];Vi=boundary.code(tuple(codes[c] for c in initial+('#',)),width)
    h=raw['history_packet']
    fixture=slope.classes.positive_outer_fixture if h['history_kind']=='slope_classes' else slope.per_tile.positive_outer_fixture
    hv=fixture(h,selection,Vi)
    values={name:1 for name in raw['parameters']+raw['auxiliaries']}
    values.update(boundary.outer_fixture(loaded,n,width))
    values.update(x=x,Ufinal=hv['Ufinal'],Vfinal=hv['Vfinal'])
    if pc=='parameter':values['program_code']=code
    if not raw['inline_initial']:values['Vinitial']=Vi
    values.update({'hist__'+name:hv[name] for name in h['auxiliaries']})
    assert all(values[name]>0 for name in raw['parameters']+raw['auxiliaries'])
    if packet['unit_product']:
        values={name:values.get(name,1) for name in packet['parameters']+packet['auxiliaries']}
        restored=slope.units.lift(packet,values)
    else:restored=values
    env=execute(raw['source'],restored);split=raw['boundary_comparisons']
    assert env['input_bottom']==Vi
    assert all(scalar(a,env)==scalar(b,env) for a,b in raw['comparisons'][:5])
    assert all(scalar(a,env)==scalar(b,env) for a,b in raw['comparisons'][split:split+3])
    a,b=raw['comparisons'][split-1];accepted=scalar(a,env)==scalar(b,env)
    assert accepted==(word==target)
    if expected is not None:assert accepted==expected
    assert boundary.dense_append(machine['tiles'],selection,codes,width,(1,Vi,1))==[hv['Ufinal'],hv['Vfinal'],1]
    return dict(input=x,loaded_input=loaded,padding=padding,recoder_duration=n,
        history_duration=len(selection),accepted=accepted,
        full_native_Pell_witnesses_materialized=False)


def verify():
    rng=random.Random(5875642);records=[];rawcases=unitcases=signed=local=0;outer=[]
    for name in ('odd','even','all','return_left'):
        spec=sample_machine(name)
        base=build_for_tm(*spec);local+=local_derivations(base['machine'])
        for inline in (False,True):
          for choice in ('per_tile','slope_classes','auto'):
            raw=build_for_tm(*spec,inline_initial=inline,unit_product=False,history_choice=choice)
            unit=build_for_tm(*spec,inline_initial=inline,history_choice=choice)
            for packet in (raw,unit):
                source,out=polynomial_source(packet);counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
                record=ledger(packet);assert len(source)==record['polynomial']['operations']
                assert counts==dict(M=record['polynomial']['multiplications'],A=record['polynomial']['additions_subtractions'])
                known=set(packet['parameters']+packet['auxiliaries'])
                for n,op,a,b in source:
                    assert n not in known and all(not isinstance(v,str) or v in known for v in (a,b));known.add(n)
                records.append(dict(machine=name,**record))
                for i in range(8):
                    values={n:rng.randrange(1,5) if i<4 else rng.randrange(-2,4) for n in packet['parameters']+packet['auxiliaries']}
                    if packet['unit_product']:slope.units.audit_identity(packet,values);unitcases+=1
                    else:
                        env=execute(source,values);rr=slope.independent_raw(packet,values)
                        assert rr==[scalar(a,env)-scalar(b,env) for a,b in packet['comparisons']]
                        assert env[out]==sum(r*r for r in rr);rawcases+=1
                    signed+=i>=4
            for x in (1,2):
                want=(bool(x&1) if name=='odd' else not bool(x&1) if name=='even' else True)
                outer.append(dict(machine=name,**outer_fixture(unit,x,int(x==1),expected=want)))
    loaders=[]
    for pc,code in (('parameter',3),('parameter',4),(8,1)):
        p=odd_machine(program_code=pc);loaders.append(ledger(p))
        outer.append(dict(machine='odd',**outer_fixture(p,1,1,code,expected=bool((code if pc=='parameter' else pc)&1))))
    variants=[]
    for factor in (False,True):
      for inline in (False,True):
       for unit in (False,True):
        variants.append(ledger(odd_machine(factor=factor,inline_initial=inline,unit_product=unit)))
    example=odd_machine();old=slope.odd_machine()
    assert example['boundary_packet']==old['boundary_packet']
    assert example['machine']['alphabet']==old['machine']['alphabet'] and example['machine']['codes']==old['machine']['codes']
    assert example['tiles']==30 and example['operations']==510
    assert ledger(example)['polynomial']==dict(operations=587,multiplications=254,additions_subtractions=333)
    assert example['witnesses']==94 and ledger(example)['degree_audit']['exact_degree']==5642
    return dict(status='PASS_GPCP_STATE_FREE_COPIES',raw_complete_identities=rawcases,
        unit_complete_identities=unitcases,signed_assignments=signed,
        local_transition_and_cleanup_derivations=local,variant_ledgers=records,
        odd_variants=variants,loader_ledgers=loaders,genuine_outer_runs=outer,
        example=dict(ledger=ledger(example),alphabet=example['machine']['alphabet'],
            copy_alphabet=example['machine']['copy_alphabet'],tile_embedding=example['machine']['tile_embedding'],
            source=example['source'],comparisons=example['comparisons'],parameters=example['parameters'],auxiliaries=example['auxiliaries']),
        scope='Complete ordinary-input equivalence for well-formed configurations, distinct start/accept and machines insensitive to every leading-zero padding. Signed arithmetic identities compare each emitted packet with its own complete component formulas, not the larger-table polynomial. Finite outer runs do not materialize full Pell witnesses. The odd example is decidable; the separate explicit Neary-Woods packet and universal75/88 bounds are unchanged.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])

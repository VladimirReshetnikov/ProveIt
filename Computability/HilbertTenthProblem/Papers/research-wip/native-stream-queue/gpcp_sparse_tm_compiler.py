"""Complete ordinary-input compilation of sparse, oriented TM rewrites.

Each changed tile table is encoded and compiled afresh.  State orientation
is fixed compiler data, and the initial state must remain before its cell.
The symbolic helper and all historical arithmetic packets stay unchanged.
"""
import argparse
from collections import Counter
from functools import lru_cache
import json
from pathlib import Path
import random

import gpcp_bracket_anchored_history as bracket
import sparse_tm_rewriting as sparse

prefix=bracket.prefix
fixed=bracket.fixed
planner=bracket.planner
boundary=bracket.boundary
execute=bracket.execute
scalar=bracket.scalar


def incoming_orientations(tape,transitions,start,accept):
    """Per-target rule-count choice, constrained to start/accept before."""
    _,states=sparse.validate_tm(tape,transitions,accept)
    incoming={s:Counter(d for p,_,d in transitions.values() if p==s) for s in states}
    score=lambda s,d:len(tape)*incoming[s][d]-int(s!=accept and incoming[s][d]>0)
    result={s:'before' if score(s,'R')>=score(s,'L') else 'after' for s in states}
    result.update({start:'before',accept:'before'})
    return result


def ordered_rules(tape,transitions,accept,orientations=None,rule_order='grouped'):
    rules=sparse.rewriting_rules_sparse(tape,transitions,accept,orientations)
    if rule_order=='helper':return rules
    assert rule_order=='grouped'
    repair_count=(len(sparse.right_repair_states(transitions,accept,orientations))+
                  len(sparse.left_repair_states(transitions,accept,orientations)))
    cut=len(rules)-repair_count-2*len(tape)
    # Only a fixed permutation: transition rules, lexicographic repairs,
    # then left-context and right-context accepting cleanup.
    result=(rules[:cut]+tuple(sorted(rules[cut:cut+repair_count]))+
            rules[-len(tape):]+rules[-2*len(tape):-len(tape)])
    assert len(result)==len(rules) and set(result)==set(rules)
    return result


def machine_table(machine,transitions,start,accept,orientations=None,rule_order='grouped'):
    tape=machine['tape'];_,active=sparse.validate_tm(tape,transitions,accept)
    states=active|{start}
    orientation=sparse.orientation_map(states,orientations)
    assert start!=accept and orientation[start]=='before', 'ordinary input requires a before-state start'
    rules=ordered_rules(tape,transitions,accept,
                        {s:orientation[s] for s in active},rule_order)
    copy=tuple(a for a in machine['alphabet'] if a in set(tape)|{'[',']'})
    result=bracket.table(dict(machine,rules=rules,copy_alphabet=copy,
        states=tuple(sorted(states)),transitions=dict(transitions),start=start,accept=accept,
        orientations=orientation,rule_order=rule_order,sparse_tm=True))
    result.pop('numeric',None)  # An inherited numeric table describes the old rules.
    return result


def build_for_tm(tape,transitions,start,accept,*,orientations=None,rule_order='grouped',
                 width=None,unit_product=True,regroup=True,factor=True,
                 history_choice='auto',**options):
    old=fixed.parent.build_for_tm(tape,transitions,start,accept,width=width,**options)
    machine=machine_table(old['machine'],transitions,start,accept,orientations,rule_order)
    codes=machine['codes'];encode=lambda w:tuple(codes[a] for a in w)
    numeric=tuple((encode(a),encode(b)) for a,b in machine['tiles'])
    # Recompile the changed map. replace_history's same-map guard is never
    # bypassed: it subsequently sees exactly this freshly built raw table.
    raw=fixed.parent.build(numeric,old['width'],encode(('[',start)),encode((']',)),
                           encode(('[',accept,']')),**options)
    raw.update(machine=machine,bracket_anchored=True,sparse_tm=True)
    return planner.rewrite(raw,unit_product=unit_product,regroup=regroup,
                           factor=factor,history_choice=history_choice)


def odd_machine(**options):
    transitions={(s,a):(('start' if a=='0' else 'odd'),a,'R')
                 for s in ('start','odd') for a in ('0','1')}
    transitions.update({('start','_'):('reject','_','S'),('odd','_'):('halt','_','S')})
    return build_for_tm(('0','1','_'),transitions,'start','halt',**options)


def universal_orientations(mode='oriented'):
    machine=prefix.parent.compiler_table();transitions=machine['transitions']
    _,states=sparse.validate_tm(machine['tape'],transitions,'halt')
    if mode=='all_before':return {s:'before' for s in states}
    assert mode=='oriented'
    result=incoming_orientations(machine['tape'],transitions,'u1','halt')
    result.update(u2='after',u3='after',u1='before',halt='before')
    return result


def universal_table(orientation_mode='oriented',rule_order='grouped'):
    machine=prefix.parent.compiler_table()
    return machine_table(machine,machine['transitions'],'u1','halt',
                         universal_orientations(orientation_mode),rule_order)


def code_map(variant='sparse_tuned'):
    if variant!='sparse_tuned':return prefix.code_map(variant)
    codes=prefix.code_map('balanced')
    for a,b in (('u10','u12'),('u4','u6'),('u7','u9')):
        codes[a],codes[b]=codes[b],codes[a]
    assert sorted(codes.values())==sorted(prefix.code_map('balanced').values())
    assert all(not b.startswith(a) for x,a in codes.items() for y,b in codes.items() if x!=y)
    return codes


def block_words(variant='sparse_tuned'):
    words=prefix.block_words('balanced' if variant=='sparse_tuned' else variant)
    codes=code_map(variant)
    assert len(prefix.bits(words[0],codes))==len(prefix.bits(words[1],codes))
    assert 0<prefix.value(words[0],codes)<prefix.value(words[1],codes)
    return words


@lru_cache(None)
def universal_history(variant='sparse_tuned',orientation_mode='oriented',rule_order='grouped'):
    codes=code_map(variant)
    append=lambda word:(1<<len(prefix.bits(word,codes)),prefix.value(word,codes))
    maps=tuple((*append(a),*append(b))
               for a,b in universal_table(orientation_mode,rule_order)['tiles'])
    return planner.choose_history(maps)


def build_universal(*,inline_initial=True,variant='sparse_tuned',orientation_mode='oriented',
                    rule_order='grouped'):
    base_variant='balanced' if variant=='sparse_tuned' else variant
    old=prefix.build(inline_initial=inline_initial,variant=base_variant)['raw_packet']
    codes=code_map(variant);h=universal_history(variant,orientation_mode,rule_order)
    assert all(codes[a]==prefix.code_map(base_variant)[a] for a in old['block_words'][0]+old['block_words'][1])
    terminal=('[','halt',']')
    updates={'terminal_scaled':('terminal_scaled','*',1<<len(prefix.bits(terminal,codes)),'Ufinal'),
             'terminal_top':('terminal_top','+','terminal_scaled',prefix.value(terminal,codes))}
    front=[updates.get(n,(n,op,a,b)) for n,op,a,b in old['source'] if not n.startswith('hist__')]
    def alias(v):
        if not isinstance(v,str):return v
        if v=='Vinitial' and inline_initial:return 'input_bottom'
        return v if v in h['parameters'] else 'hist__'+v
    source=front+[('hist__'+n,op,alias(a),alias(b)) for n,op,a,b in h['source']]
    pairs=old['comparisons'][:old['boundary_comparisons']]+[(alias(a),alias(b)) for a,b in h['comparisons']]
    aux=[a for a in old['auxiliaries'] if not a.startswith('hist__')]+['hist__'+a for a in h['auxiliaries']]
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    raw=dict(old,source=source,comparisons=pairs,auxiliaries=aux,history_packet=h,
        tiles=len(h['maps']),layout=h['layout'],operations=len(source),
        multiplications=counts['M'],additions_subtractions=counts['A'],
        equations=len(pairs),witnesses=len(aux),bracket_anchored=True,sparse_tm=True,
        terminal_word=terminal,terminal_bits=prefix.bits(terminal,codes),
        binary_prefix_code=codes,code_variant=variant,
        orientation_mode=orientation_mode,rule_order=rule_order)
    raw.pop('terminal',None)
    packet=prefix.units.rewrite(raw)
    packet.update(machine=universal_table(orientation_mode,rule_order),sparse_tm=True,unit_product=True,
                  orientation_mode=orientation_mode,rule_order=rule_order)
    return packet


def program_parameters(q,h,productions,right_index,left_index,variant='sparse_tuned'):
    _,initial_prefix,suffix=prefix.parent.program_parameters(q,h,productions,right_index,left_index)
    assert suffix[-1]=='#';suffix=suffix[:-1];codes=code_map(variant)
    values=dict(program_prefix=prefix.sentinel(initial_prefix,codes),
        program_suffix_scale=1<<len(prefix.bits(suffix,codes)),
        program_suffix_value=prefix.value(suffix,codes))
    assert min(values.values())>0
    return values,initial_prefix,suffix


def polynomial_source(packet):return planner.polynomial_source(packet)


def ledger(packet):
    result=planner.ledger(packet)
    return dict(result,sparse_tm=True,orientations=packet['machine']['orientations'])


def universal_ledger(packet):
    return dict(prefix.ledger(packet),sparse_tm=True,tiles=packet['tiles'],
                orientation_mode=packet['orientation_mode'],rule_order=packet['rule_order'])


def source_audit(packet,record,rng,cases=8):
    source,out=polynomial_source(packet)
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    assert len(source)==record['polynomial']['operations']
    assert counts==dict(M=record['polynomial']['multiplications'],A=record['polynomial']['additions_subtractions'])
    known=set(packet['parameters']+packet['auxiliaries'])
    for name,op,a,b in source:
        assert name not in known and all(isinstance(v,int) or v in known for v in (a,b))
        known.add(name)
    for case in range(cases):
        values={n:rng.randrange(1,4) if case<cases//2 else rng.randrange(-2,4)
                for n in packet['parameters']+packet['auxiliaries']}
        if packet['unit_product']:planner.units.audit_identity(packet,values)
        else:
            env=execute(source,values);residuals=planner.independent_raw(packet,values)
            assert residuals==[scalar(a,env)-scalar(b,env) for a,b in packet['comparisons']]
            assert env[out]==sum(r*r for r in residuals)
    return cases


def local_derivations(machine):
    """Every emitted rule gives a bracket-coded row, including pending rows."""
    count=0;tape=machine['tape']
    for ri,(lhs,rhs) in enumerate(machine['rules']):
        for left,right in (((),()),((tape[0],),(tape[-1],)),((tape[-1],tape[0]),(tape[0],))):
            begin=() if lhs[0]=='[' else ('[',)+left
            end=() if lhs[-1]==']' else right+(']',)
            initial=begin+lhs+end;target=begin+rhs+end
            steps=[(ri,len(begin),target)]
            selection=bracket.encode_derivation(machine,initial,steps)
            assert bracket.decode_solution(machine,initial,target,selection)==steps
            count+=1
    for left,right in (((),(tape[0],)),((tape[0],),()),((tape[0],tape[-1]),(tape[-1],))):
        initial=('[',)+left+(machine['accept'],)+right+(']',)
        selection,accepted=bracket.finite_run(machine,initial,('[',machine['accept'],']'))
        assert accepted and selection;count+=1
    return count


def outer_fixture(packet,x,padding=0,code=1,expected=None):
    raw=packet['raw_packet'] if packet['unit_product'] else packet
    machine=raw['machine'];pc=raw['program_code'];width=raw['width']
    loaded=x if pc is None else (code if pc=='parameter' else pc)*(2*x+1)
    n=max(2,loaded.bit_length()+padding)
    initial=('[',machine['start'])+tuple(bin(loaded)[2:].zfill(n))+(']',)
    target=('[',machine['accept'],']')
    selection,accepted=bracket.finite_run(machine,initial,target,limit=20*n+64)
    if expected is not None:assert accepted==expected
    codes=machine['codes'];Vi=boundary.code(tuple(codes[a] for a in initial),width)
    h=raw['history_packet']
    fixture=planner.classes.positive_outer_fixture if h['history_kind']=='slope_classes' else planner.per_tile.positive_outer_fixture
    hv=fixture(h,selection,Vi)
    values={name:1 for name in raw['parameters']+raw['auxiliaries']}
    values.update(boundary.outer_fixture(loaded,n,width))
    values.update(x=x,Ufinal=hv['Ufinal'],Vfinal=hv['Vfinal'])
    if pc=='parameter':values['program_code']=code
    if not raw['inline_initial']:values['Vinitial']=Vi
    values.update({'hist__'+name:hv[name] for name in h['auxiliaries']})
    assert min(values[name] for name in raw['parameters']+raw['auxiliaries'])>0
    if packet['unit_product']:
        values=planner.units.lift(packet,{name:values.get(name,1) for name in packet['parameters']+packet['auxiliaries']})
    env=execute(raw['source'],values);split=raw['boundary_comparisons']
    assert env['input_bottom']==Vi
    assert all(scalar(a,env)==scalar(b,env) for a,b in raw['comparisons'][:5])
    assert all(scalar(a,env)==scalar(b,env) for a,b in raw['comparisons'][split:split+3])
    a,b=raw['comparisons'][split-1];assert (scalar(a,env)==scalar(b,env))==accepted
    assert boundary.dense_append(machine['tiles'],selection,codes,width,(1,Vi,1))==[hv['Ufinal'],hv['Vfinal'],1]
    return dict(input=x,padding=padding,loaded_input=loaded,accepted=accepted,
        recoder_duration=n,history_duration=len(selection),full_native_Pell_witnesses_materialized=False)


def verify():
    rng=random.Random(815130394);records=[];identities=local=frames=words=0;outer=[]
    for name in ('odd','even','all','return_left'):
        tape,t,start,accept=fixed.sample_machine(name)
        for mode in ('all_before','incoming'):
            orientation=None if mode=='all_before' else incoming_orientations(tape,t,start,accept)
            for inline in (False,True):
              for unit in (False,True):
                packet=build_for_tm(tape,t,start,accept,orientations=orientation,
                                    inline_initial=inline,unit_product=unit)
                record=ledger(packet);records.append(dict(machine=name,orientation_mode=mode,**record))
                identities+=source_audit(packet,record,rng)
            packet=build_for_tm(tape,t,start,accept,orientations=orientation)
            local+=local_derivations(packet['machine'])
            for x in range(1,7):
              for padding in (0,2):
                expected=(bool(x&1) if name=='odd' else not bool(x&1) if name=='even' else True)
                outer.append(dict(machine=name,orientation_mode=mode,
                                  **outer_fixture(packet,x,padding,expected=expected)))
    variants=[]
    for choice in ('per_tile','slope_classes'):
      for inline in (False,True):
        packet=odd_machine(history_choice=choice,inline_initial=inline)
        rec=ledger(packet);variants.append(rec);identities+=source_audit(packet,rec,rng)
    loaders=[]
    for pc,code in (('parameter',3),('parameter',4),(8,1)):
        packet=odd_machine(program_code=pc);rec=ledger(packet);loaders.append(rec)
        identities+=source_audit(packet,rec,rng)
        outer.append(dict(machine='odd',orientation_mode='all_before',
                          **outer_fixture(packet,1,1,code,expected=bool((code if pc=='parameter' else pc)&1))))
    # The alphabet can retain a declared isolated start; no fake acceptance.
    isolated=build_for_tm(('0','1','_'),{},'isolated','halt')
    assert not sparse.successors(('[','isolated','0',']'),isolated['machine']['rules'])
    rejected=False
    try:build_for_tm(('0','1','_'),{},'isolated','halt',orientations={'isolated':'after'})
    except AssertionError:rejected=True
    assert rejected
    universal_records=[];example=None
    for mode in ('all_before','oriented'):
        machine=universal_table(mode);local+=local_derivations(machine)
        for variant in ('tuned','balanced','sparse_tuned'):
            codes=code_map(variant);h=universal_history(variant,mode)
            for inline in (False,True):
                packet=build_universal(inline_initial=inline,variant=variant,orientation_mode=mode)
                rec=universal_ledger(packet);universal_records.append(rec)
                identities+=source_audit(packet,rec,rng,12)
                if mode=='oriented' and variant=='sparse_tuned' and inline:
                    source,out=polynomial_source(packet)
                    example=dict(ledger=rec,source=packet['source'],comparisons=packet['comparisons'],
                        parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],
                        polynomial_finalizer=source[packet['operations']:],polynomial_output=out,
                        binary_prefix_code=codes,orientations=machine['orientations'],
                        tiles=machine['tiles'],maps=h['maps'],history_ledger=planner.history_ledger(h))
            for _ in range(48):
                selection=[rng.randrange(len(machine['tiles'])) for _ in range(rng.randrange(1,24))]
                top,bottom=boundary.selected_images(machine['tiles'],selection)
                vi=rng.randrange(1,30);U,V=1,vi
                for i in selection:
                    a,c,b,d=h['maps'][i];U,V=a*U+c,b*V+d
                assert U==prefix.sentinel(top,codes)
                assert V==vi*(1<<len(prefix.bits(bottom,codes)))+prefix.value(bottom,codes)
                assert prefix.decode(prefix.bits(top,codes),codes)==top
                assert prefix.decode(prefix.bits(bottom,codes),codes)==bottom;words+=1
            for _ in range(48):
                q=rng.randrange(4,8);productions={(1,i):(i,2) for i in range(1,q+1)}
                params,left,right=program_parameters(q,2,productions,q-1,q,variant)
                n=rng.randrange(2,25);x=rng.randrange(1,1<<n);blocks=block_words(variant)
                physical=sum((blocks[int(bit)] for bit in bin(x)[2:].zfill(n)),())
                k=len(prefix.bits(blocks[0],codes));Q=1<<(k*n);R=(Q-1)//((1<<k)-1)
                c0,c1=(prefix.value(w,codes) for w in blocks)
                D=c0*R+(c1-c0)*boundary.spread(x,k)
                Vi=(params['program_prefix']*Q+D)*params['program_suffix_scale']+params['program_suffix_value']
                initial=left+physical+right
                assert bracket.valid(initial,machine) and Vi==prefix.sentinel(initial,codes)
                assert machine['orientations']['u1']=='before';frames+=1
    assert example['ledger']['polynomial']==dict(operations=810,multiplications=349,additions_subtractions=461)
    assert example['ledger']['witnesses']==125 and example['ledger']['exact_degree']==130394
    assert len(universal_table('all_before')['tiles'])==75 and len(universal_table()['tiles'])==57
    return dict(status='PASS_GPCP_SPARSE_TM_COMPILER',generic_ledgers=records,
        history_choice_ledgers=variants,loader_ledgers=loaders,odd_example=ledger(odd_machine()),
        universal_ledgers=universal_records,full_source_identities=identities,
        signed_source_assignments=identities//2,local_rule_and_cleanup_rows=local,
        positive_outer_runs=outer,positive_program_frames=frames,
        independent_tile_word_and_prefix_checks=words,isolated_start_rejects=True,
        after_initial_orientation_rejected=True,example=example,
        scope='Complete acceptance equivalence for normalized valid starts with initial before-state and distinct accept. Ordinary U15 input bridge and independent positive native extensions are retained. Finite outer fixtures check only the first five recoder equations, three history equations, terminal comparison, and dense append/positive coordinates; no full numerical Pell witnesses are claimed.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
    print('odd',result['odd_example'])
    for rec in result['universal_ledgers']:
        print(rec['orientation_mode'],rec['code_variant'],rec['inline_initial'],
              rec['polynomial'],rec['witnesses'],rec['exact_degree'])

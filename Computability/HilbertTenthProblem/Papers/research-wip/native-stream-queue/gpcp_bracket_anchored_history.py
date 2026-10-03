"""Complete histories using the configuration brackets as row boundaries.

No fresh separator occurs in the table or either endpoint. Soundness uses
nonempty left sides, anchored brackets, one state per configuration, and
the absence of state-copy tiles; it is not a theorem for arbitrary GPCP.
"""
import argparse
from collections import Counter
from functools import lru_cache
import json
from pathlib import Path
import random

import gpcp_state_free_copies as fixed
import neary_woods_prefix_universal as prefix

planner=prefix.planner
execute=prefix.execute
scalar=prefix.scalar
boundary=fixed.boundary


def table(machine):
    copy=tuple(a for a in machine['copy_alphabet'] if a!='#')
    rules=machine['rules'];states=set(machine.get('states',()))
    if not states:
        states=set(machine['alphabet'])-set(machine['copy_alphabet'])
    assert states and not states.intersection(copy)
    for lhs,rhs in rules:
        for word in (lhs,rhs):
            assert word and '#' not in word
            assert sum(a in states for a in word)==1
            assert '[' not in word[1:] and ']' not in word[:-1]
    # The older helper requires a fresh '#'; this table uses the bracket
    # theorem below and deliberately has no such copy tile.
    tiles=tuple(((a,),(a,)) for a in copy)+tuple(rules)
    assert all('#' not in a+b for a,b in tiles)
    return dict(machine,copy_alphabet=copy,tiles=tiles,states=tuple(sorted(states)))


def valid(word,machine):
    return (len(word)>=3 and word[0]=='[' and word[-1]==']'
            and word.count('[')==word.count(']')==1 and '#' not in word
            and sum(a in machine['states'] for a in word)==1
            and all(a in set(machine['tape'])|set(machine['states']) for a in word[1:-1]))


def encode_derivation(machine,initial,steps):
    """Concatenate the ordinary tile rows, without separator copies."""
    assert valid(initial,machine) and steps
    copies={a:i for i,a in enumerate(machine['copy_alphabet'])}
    word=initial;selection=[]
    for ri,at,target in steps:
        lhs,rhs=machine['rules'][ri]
        assert word[at:at+len(lhs)]==lhs
        assert word[:at]+rhs+word[at+len(lhs):]==target and valid(target,machine)
        selection.extend(copies[a] for a in word[:at])
        selection.append(len(copies)+ri)
        selection.extend(copies[a] for a in word[at+len(lhs):])
        word=target
    a,b=boundary.selected_images(machine['tiles'],selection)
    assert a+word==initial+b
    return selection


def decode_solution(machine,initial,target,selection):
    """Finite counterpart of the bracket-cut converse proved in the note."""
    assert valid(initial,machine) and valid(target,machine)
    a,b=boundary.selected_images(machine['tiles'],selection)
    assert a+target==initial+b
    word=initial;remaining=list(selection);steps=[]
    while remaining:
        upper=();lower=();cut=0;rule_at=[]
        while len(upper)<len(word):
            assert cut<len(remaining),'target would start a second bracket inside the configuration'
            index=remaining[cut];lhs,rhs=machine['tiles'][index]
            if index>=len(machine['copy_alphabet']):
                rule_at.append((index-len(machine['copy_alphabet']),len(upper)))
            upper+=lhs;lower+=rhs;cut+=1
        assert upper==word and len(rule_at)==1 and valid(lower,machine)
        ri,at=rule_at[0];lhs,rhs=machine['rules'][ri]
        assert word[:at]+rhs+word[at+len(lhs):]==lower
        steps.append((ri,at,lower));word=lower;remaining=remaining[cut:]
        a,b=boundary.selected_images(machine['tiles'],remaining)
        assert a+target==word+b
    assert word==target
    return steps


def build_for_tm(tape,transitions,start,accept,*,width=None,unit_product=True,
                 regroup=True,factor=True,history_choice='auto',**options):
    old=fixed.parent.build_for_tm(tape,transitions,start,accept,width=width,**options)
    machine=old['machine']
    machine=table(dict(machine,copy_alphabet=tuple(a for a in machine['alphabet']
                        if a in set(tape)|{'[',']','#'})))
    codes=machine['codes'];encode=lambda word:tuple(codes[a] for a in word)
    numeric=tuple((encode(a),encode(b)) for a,b in machine['tiles'])
    raw=fixed.parent.build(numeric,old['width'],encode(('[',start)),encode((']',)),
                           encode(('[',accept,']')),**options)
    raw.update(machine=machine,bracket_anchored=True)
    return planner.rewrite(raw,unit_product=unit_product,regroup=regroup,
                           factor=factor,history_choice=history_choice)


def odd_machine(**options):
    t={(s,a):(('start' if a=='0' else 'odd'),a,'R')
       for s in ('start','odd') for a in ('0','1')}
    t.update({('start','_'):('reject','_','S'),('odd','_'):('halt','_','S')})
    return build_for_tm(('0','1','_'),t,'start','halt',**options)


def universal_table():
    return table(prefix.parent.compiler_table())


@lru_cache(None)
def universal_history(variant='tuned'):
    codes=prefix.code_map(variant)
    append=lambda w:(1<<len(prefix.bits(w,codes)),prefix.value(w,codes))
    maps=tuple((*append(a),*append(b)) for a,b in universal_table()['tiles'])
    return planner.choose_history(maps)


def build_universal(*,inline_initial=True,variant='tuned'):
    old=prefix.build(inline_initial=inline_initial,variant=variant)['raw_packet']
    codes=prefix.code_map(variant);h=universal_history(variant);terminal=('[','halt',']')
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
    cc=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    raw=dict(old,source=source,comparisons=pairs,auxiliaries=aux,history_packet=h,
             tiles=len(h['maps']),layout=h['layout'],operations=len(source),
             multiplications=cc['M'],additions_subtractions=cc['A'],
             equations=len(pairs),witnesses=len(aux),bracket_anchored=True,
             terminal_word=terminal,terminal_bits=prefix.bits(terminal,codes))
    raw.pop('terminal',None)
    known=set(raw['parameters']+aux)
    for n,op,a,b in source:
        assert n not in known and all(isinstance(v,int) or v in known for v in (a,b))
        known.add(n)
    packet=prefix.units.rewrite(raw)
    packet.update(machine=universal_table(),bracket_anchored=True)
    return packet


def program_parameters(q,h,productions,right_index,left_index,variant='tuned'):
    _,initial_prefix,suffix=prefix.program_parameters(q,h,productions,right_index,left_index,variant)
    assert suffix[-1]=='#';suffix=suffix[:-1];codes=prefix.code_map(variant)
    values=dict(program_prefix=prefix.sentinel(initial_prefix,codes),
        program_suffix_scale=1<<len(prefix.bits(suffix,codes)),
        program_suffix_value=prefix.value(suffix,codes))
    assert min(values.values())>0
    return values,initial_prefix,suffix


def universal_ledger(packet):
    return dict(prefix.ledger(packet),bracket_anchored=True,tiles=packet['tiles'])


def finite_run(machine,initial,target,limit=500):
    word=initial;steps=[]
    for _ in range(limit):
        if word==target:break
        choices=boundary.successors(word,machine['rules'])
        if not choices:break
        step=choices[0];steps.append(step);word=step[2]
    assert steps
    selection=encode_derivation(machine,initial,steps)
    assert decode_solution(machine,initial,word,selection)==steps
    upper,lower=boundary.selected_images(machine['tiles'],selection)
    assert (upper+target==initial+lower)==(word==target)
    return selection,word==target


def verify():
    rng=random.Random(10467332);identities=frames=words=0;records=[];runs=[]
    for name in ('odd','even','all','return_left'):
        spec=fixed.sample_machine(name)
        for inline in (False,True):
            for unit in (False,True):
                p=build_for_tm(*spec,inline_initial=inline,unit_product=unit)
                rec=planner.ledger(p);records.append(dict(machine=name,**rec))
                for _ in range(6):
                    values={n:rng.randrange(-2,4) for n in p['parameters']+p['auxiliaries']}
                    if unit:planner.units.audit_identity(p,values)
                    else:
                        source,out=planner.polynomial_source(p);env=execute(source,values)
                        rr=planner.independent_raw(p,values)
                        assert rr==[scalar(a,env)-scalar(b,env) for a,b in p['comparisons']]
                        assert env[out]==sum(a*a for a in rr)
                    identities+=1
        p=build_for_tm(*spec);machine=p['machine'];codes=machine['codes'];width=p['width']
        for x in range(1,7):
          for padding in (0,2):
            n=max(2,x.bit_length()+padding)
            initial=('[',machine['start'])+tuple(bin(x)[2:].zfill(n))+(']',)
            target=('[',machine['accept'],']')
            selection,accepted=finite_run(machine,initial,target)
            expected=(bool(x&1) if name=='odd' else not bool(x&1) if name=='even' else True)
            assert accepted==expected
            Vi=boundary.code(tuple(codes[a] for a in initial),width)
            h=p['raw_packet']['history_packet'];v=planner.classes.positive_outer_fixture(h,selection,Vi)
            assert boundary.dense_append(machine['tiles'],selection,codes,width,(1,Vi,1))==[v['Ufinal'],v['Vfinal'],1]
            runs.append(dict(machine=name,input=x,padding=padding,accepted=accepted,tiles=len(selection)))
    universals=[];example=None
    for variant in ('balanced','tuned'):
        codes=prefix.code_map(variant);machine=universal_table()
        for inline in (False,True):
            p=build_universal(inline_initial=inline,variant=variant)
            rec=universal_ledger(p);universals.append(rec)
            source,out=prefix.units.polynomial_source(p)
            counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
            assert len(source)==rec['polynomial']['operations']
            assert counts==dict(M=rec['polynomial']['multiplications'],A=rec['polynomial']['additions_subtractions'])
            for _ in range(12):
                values={n:rng.randrange(-2,4) for n in p['parameters']+p['auxiliaries']}
                prefix.units.audit_identity(p,values);identities+=1
            if variant=='tuned' and inline:
                example=dict(ledger=rec,source=p['source'],comparisons=p['comparisons'],
                    parameters=p['parameters'],auxiliaries=p['auxiliaries'],
                    polynomial_finalizer=source[p['operations']:],polynomial_output=out,
                    binary_prefix_code=codes,tiles=machine['tiles'],maps=p['history_packet']['maps'])
        for _ in range(96):
            q=rng.randrange(4,8);prod={(1,i):(i,2) for i in range(1,q+1)}
            params,initial_prefix,suffix=program_parameters(q,2,prod,q-1,q,variant)
            n=rng.randrange(2,20);x=rng.randrange(1,1<<n);blocks=prefix.block_words(variant)
            physical=sum((blocks[int(bit)] for bit in bin(x)[2:].zfill(n)),())
            k=len(prefix.bits(blocks[0],codes));Q=1<<(k*n);R=(Q-1)//((1<<k)-1)
            c0,c1=[prefix.value(b,codes) for b in blocks]
            D=c0*R+(c1-c0)*boundary.spread(x,k)
            Vi=(params['program_prefix']*Q+D)*params['program_suffix_scale']+params['program_suffix_value']
            initial=initial_prefix+physical+suffix
            assert '#' not in initial and valid(initial,machine)
            assert Vi==prefix.sentinel(initial,codes);frames+=1
        for _ in range(96):
            selection=[rng.randrange(len(machine['tiles'])) for _ in range(rng.randrange(1,30))]
            top,bottom=boundary.selected_images(machine['tiles'],selection)
            vi=rng.randrange(1,30);U,V=1,vi
            for i in selection:
                a,c,b,d=universal_history(variant)['maps'][i];U=a*U+c;V=b*V+d
            assert U==prefix.sentinel(top,codes)
            assert V==vi*(1<<len(prefix.bits(bottom,codes)))+prefix.value(bottom,codes)
            assert prefix.decode(prefix.bits(top,codes),codes)==top
            assert prefix.decode(prefix.bits(bottom,codes),codes)==bottom;words+=1
    assert example['ledger']['polynomial']['operations']==1046
    return dict(status='PASS_GPCP_BRACKET_ANCHORED_HISTORY',complete_signed_identities=identities,
        generic_ledgers=records,odd_example=planner.ledger(odd_machine()),
        finite_runs=runs,universal_ledgers=universals,positive_program_frames=frames,
        word_append_and_injection_cases=words,example=example,
        scope='Bracket-cut proof gives complete well-formed acceptance equivalence without fresh separators. Universality inherits the same paid prefix-code ordinary-input bridge on valid program slices. Finite tests leave native Pell witnesses unmaterialized.')


if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--write',action='store_true');args=ap.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print('odd',result['odd_example']['polynomial'])
    for p in result['universal_ledgers']:print(p['code_variant'],p['inline_initial'],p['polynomial'],p['witnesses'],p['exact_degree'])

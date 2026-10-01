"""Prefix-coded U15,2: complete ordinary-input universal polynomial.

The prefix code is fixed compiler data.  It changes input block width and
tile affine maps; it does not assert an identity of the old numeric source.
"""
import argparse
from collections import Counter
from functools import lru_cache
import json
from pathlib import Path
import random

import neary_woods_explicit_universal_tm as parent

execute=parent.execute
scalar=parent.scalar
units=parent.units
history=parent.history
planner=parent.slope


def code_map(variant='tuned'):
    symbols=parent.compiler_table()['alphabet']
    if variant=='tuned':
        result={'_':'00','b':'01',
            'u1':'10010','u2':'10001','u3':'11110','u4':'11101','u5':'10011',
            'u6':'11011','u7':'11010','u8':'11001','u9':'10000','u10':'11100',
            'u11':'10100','u12':'10110','u13':'10101','u14':'10111','u15':'11000',
            '[':'1111101',']':'1111110','#':'1111111','halt':'1111100'}
    elif variant=='balanced':
        result={'_':'00','b':'01'}
        result.update({f'u{i}':'1'+format(i-1,'04b') for i in range(1,16)})
        result.update({a:'11111'+format(i,'02b') for i,a in enumerate(('[',']','#','halt'))})
    elif variant=='uniform_nontape':
        result={'_':'00','b':'01',**{a:'1'+format(i,'05b') for i,a in enumerate(symbols[2:])}}
    elif variant=='short_blank':
        result={'_':'0','b':'10',**{a:'11'+format(i,'05b') for i,a in enumerate(symbols[2:])}}
    elif variant=='short_b':
        result={'_':'10','b':'0',**{a:'11'+format(i,'05b') for i,a in enumerate(symbols[2:])}}
    else:raise ValueError(variant)
    assert set(result)==set(symbols)
    assert all(set(code)<={'0','1'} and code for code in result.values())
    assert all(not right.startswith(left) for a,left in result.items() for b,right in result.items() if a!=b)
    return result


def bits(word,codes):return ''.join(codes[s] for s in word)


def value(word,codes):
    text=bits(word,codes)
    return int(text,2) if text else 0


def sentinel(word,codes):return (1<<len(bits(word,codes)))+value(word,codes)


def decode(text,codes):
    inverse={v:k for k,v in codes.items()};answer=[];buffer=''
    for letter in text:
        assert letter in '01';buffer+=letter
        if buffer in inverse:answer.append(inverse[buffer]);buffer=''
        else:assert any(code.startswith(buffer) for code in inverse)
    assert not buffer
    return tuple(answer)


def block_words(variant='tuned'):
    words=[tuple('_' if a=='c' else a for a in word) for word in parent.bit_blocks()]
    codes=code_map(variant)
    if value(words[0],codes)>value(words[1],codes):words.reverse()
    assert len(bits(words[0],codes))==len(bits(words[1],codes))
    assert 0<value(words[0],codes)<value(words[1],codes)
    return tuple(words)


def affine_maps(codes):
    tiles=parent.compiler_table()['tiles']
    append=lambda word:(1<<len(bits(word,codes)),value(word,codes))
    return tuple((*append(a),*append(b)) for a,b in tiles)


@lru_cache(None)
def chosen_history(variant='tuned'):
    return planner.choose_history(affine_maps(code_map(variant)))


def build(*,inline_initial=True,variant='tuned'):
    # Start from the original complete raw interface, replace the recoder
    # and boundary constants, then compose a new history of the coded tiles.
    old=parent.build(inline_initial=inline_initial,optimized=False,state_copies=False)['raw_packet']
    codes=code_map(variant);blocks=block_words(variant)
    k=len(bits(blocks[0],codes));c0,c1=(value(word,codes) for word in blocks)
    left=parent.boundary.recoder(k);right=chosen_history(variant)
    prefix=[row for row in old['source'] if not row[0].startswith('hist__')]
    old_recoder=parent.boundary.recoder(old['width'])
    assert prefix[:old_recoder['operations']]==old_recoder['source']
    terminal=('#','[','halt',']')
    updates={
        'input_repunit_scaled':('input_repunit_scaled','*',(1<<k)-1,'input_repunit'),
        'zero_blocks':('zero_blocks','*',c0,'input_repunit'),
        'one_correction':('one_correction','*',c1-c0,'z'),
        'terminal_scaled':('terminal_scaled','*',1<<len(bits(terminal,codes)),'Ufinal'),
        'terminal_top':('terminal_top','+','terminal_scaled',value(terminal,codes))}
    prefix=left['source']+[updates.get(n,(n,op,a,b))
        for n,op,a,b in prefix[old_recoder['operations']:]]
    def alias(v):
        if isinstance(v,int):return v
        if v=='Vinitial' and inline_initial:return 'input_bottom'
        return v if v in right['parameters'] else 'hist__'+v
    source=prefix+[('hist__'+n,op,alias(a),alias(b)) for n,op,a,b in right['source']]
    pairs=old['comparisons'][:old['boundary_comparisons']]+[(alias(a),alias(b)) for a,b in right['comparisons']]
    aux=[n for n in old['auxiliaries'] if not n.startswith('hist__')]+['hist__'+n for n in right['auxiliaries']]
    known=set(old['parameters']+aux)
    for n,op,a,b in source:
        assert n not in known and all(isinstance(v,int) or v in known for v in (a,b))
        known.add(n)
    cc=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    raw=dict(old,source=source,comparisons=pairs,auxiliaries=aux,width=k,
        symbol_width=None,binary_prefix_code=codes,block_values=[c0,c1],
        block_words=blocks,boundary_packet=left,history_packet=right,layout=right['layout'],
        operations=len(source),multiplications=cc['M'],additions_subtractions=cc['A'],
        equations=len(pairs),witnesses=len(aux),code_variant=variant,
        terminal_word=terminal,terminal_bits=bits(terminal,codes))
    raw.pop('terminal',None)
    packet=units.rewrite(raw)
    packet.update(code_variant=variant,binary_prefix_code=codes,block_words=blocks)
    return packet


def program_parameters(q,h,productions,right_index,left_index,variant='tuned'):
    # The same physical frame is used. short_b reverses the bit-pair input
    # convention; the represented semidecider must use that convention.
    _,prefix,suffix=parent.program_parameters(q,h,productions,right_index,left_index)
    codes=code_map(variant)
    params=dict(program_prefix=sentinel(prefix,codes),
                program_suffix_scale=1<<len(bits(suffix,codes)),
                program_suffix_value=value(suffix,codes))
    assert all(v>0 for v in params.values())
    return params,prefix,suffix


def ledger(packet):
    result=units.ledger(packet)
    result.update(code_variant=packet['code_variant'],
        selected_products=packet['history_packet']['selected_products'],
        history_operations=packet['history_packet']['operations'],
        **parent.degree_audit(packet))
    return result


def verify():
    rng=random.Random(10657332);records=[];examples=[];identities=0;wordcases=0;framecases=0;tilecases=0
    info=parent.compiler_table();variants=('tuned','balanced','uniform_nontape','short_blank','short_b')
    for variant in variants:
        codes=code_map(variant);blocks=block_words(variant);k=len(bits(blocks[0],codes))
        for _ in range(128):
            word=tuple(rng.choice(info['alphabet']) for _ in range(rng.randrange(1,60)))
            assert decode(bits(word,codes),codes)==word
            cut=rng.randrange(len(word)+1)
            assert bits(word[:cut],codes)+bits(word[cut:],codes)==bits(word,codes)
            assert (sentinel(word[:cut],codes)*(1<<len(bits(word[cut:],codes)))+
                    value(word[cut:],codes))==sentinel(word,codes)
            wordcases+=1
        maps=affine_maps(codes)
        for _ in range(96):
            selected=[rng.randrange(len(info['tiles'])) for _ in range(rng.randrange(1,24))]
            initial=tuple(rng.choice(info['alphabet']) for _ in range(rng.randrange(1,8)))
            U,V=1,sentinel(initial,codes)
            for tile in selected:
                a,c,b,d=maps[tile];U,V=a*U+c,b*V+d
            top,bottom=parent.boundary.selected_images(info['tiles'],selected)
            assert U==sentinel(top,codes) and V==sentinel(initial+bottom,codes)
            assert decode(bin(U)[3:],codes)==top
            assert decode(bin(V)[3:],codes)==initial+bottom
            tilecases+=1
        productions={(1,i):(i,2) for i in range(1,6)}
        params,prefix,suffix=program_parameters(5,2,productions,3,4,variant)
        for _ in range(96):
            n=rng.randrange(2,50);x=rng.randrange(1,1<<n);Q=1<<(k*n)
            R=(Q-1)//((1<<k)-1);z=parent.boundary.spread(x,k)
            c0,c1=(value(w,codes) for w in blocks)
            D=c0*R+(c1-c0)*z
            physical=tuple(a for bit in bin(x)[2:].zfill(n) for a in blocks[int(bit)])
            assert D==value(physical,codes) and 0<D<Q
            loaded=(params['program_prefix']*Q+D)*params['program_suffix_scale']+params['program_suffix_value']
            assert loaded==sentinel(prefix+physical+suffix,codes)
            assert decode(bits(prefix+physical+suffix,codes),codes)==prefix+physical+suffix
            framecases+=1
        for inline in (False,True):
            p=build(inline_initial=inline,variant=variant);record=ledger(p);records.append(record)
            source,out=units.polynomial_source(p)
            cc=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
            assert len(source)==record['polynomial']['operations']
            assert cc=={'M':record['polynomial']['multiplications'],'A':record['polynomial']['additions_subtractions']}
            for case in range(12):
                values={name:rng.randrange(1,4) if case<8 else rng.randrange(-2,4)
                        for name in p['parameters']+p['auxiliaries']}
                units.audit_identity(p,values);identities+=1
            if variant=='tuned' and inline:
                examples.append(dict(ledger=record,source=p['source'],comparisons=p['comparisons'],
                    parameters=p['parameters'],auxiliaries=p['auxiliaries'],
                    polynomial_finalizer=source[p['operations']:],polynomial_output=out,
                    code_map=codes,maps=p['history_packet']['maps'],
                    history_candidates=p['history_packet']['history_candidates']))
    return dict(status='PASS_NEARY_WOODS_PREFIX_UNIVERSAL',records=records,
        code_maps={name:code_map(name) for name in variants},
        word_morphism_and_sentinel_checks=wordcases,positive_frames=framecases,
        independent_complete_tile_words=tilecases,
        full_source_unit_identities=identities,example=examples[0],
        scope='Complete paid ordinary-input universality on valid fixed program slices. Prefix-code injectivity preserves the same physical U15,2 tile equations; native and selector coordinates need fresh positive extensions. No identity of old and new numeric witnesses is asserted.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
    for record in result['records']:print(record['code_variant'],record['inline_initial'],record['polynomial'],record['witnesses'],record['exact_degree'])

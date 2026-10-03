"""A paid rewrite-rule permutation for the complete sparse universal compiler.

Copies retain their order. Every physical rewrite is retained exactly once;
changed selector masks and native histories are compiled afresh.
"""
import argparse
from collections import Counter
from functools import lru_cache
import json
from pathlib import Path
import random

import gpcp_sparse_tm_compiler as parent

prefix=parent.prefix
planner=parent.planner
execute=parent.execute
scalar=parent.scalar


def affine_pair(pair,codes):
    append=lambda word:(1<<len(prefix.bits(word,codes)),prefix.value(word,codes))
    return (*append(pair[0]),*append(pair[1]))


def ordered_table(variant='sparse_tuned'):
    old=parent.universal_table();codes=parent.code_map(variant)
    maps=[affine_pair(pair,codes) for pair in old['rules']]
    order=tuple(sorted(range(len(maps)),key=lambda j:(maps[j][0],maps[j][2],maps[j][1]),reverse=True))
    rules=tuple(old['rules'][j] for j in order)
    assert len(rules)==len(old['rules']) and set(rules)==set(old['rules'])
    packet=parent.bracket.table(dict(old,rules=rules,rule_order='reverse_slope_pair_offset',
                                    parent_rule_permutation=order))
    k=len(old['copy_alphabet'])
    permutation=tuple(range(k))+tuple(k+j for j in order)
    assert packet['tiles']==tuple(old['tiles'][j] for j in permutation)
    packet['parent_tile_permutation']=permutation
    return packet


@lru_cache(None)
def history(variant='sparse_tuned'):
    codes=parent.code_map(variant)
    return planner.choose_history(tuple(affine_pair(pair,codes) for pair in ordered_table(variant)['tiles']))


def build(*,inline_initial=True,variant='sparse_tuned'):
    previous=parent.build_universal(inline_initial=inline_initial,variant=variant)
    old=previous['raw_packet'];h=history(variant);machine=ordered_table(variant)
    def alias(value):
        if not isinstance(value,str):return value
        if value=='Vinitial' and inline_initial:return 'input_bottom'
        return value if value in h['parameters'] else 'hist__'+value
    front=[row for row in old['source'] if not row[0].startswith('hist__')]
    source=front+[('hist__'+n,op,alias(a),alias(b)) for n,op,a,b in h['source']]
    pairs=old['comparisons'][:old['boundary_comparisons']]+[(alias(a),alias(b)) for a,b in h['comparisons']]
    aux=[n for n in old['auxiliaries'] if not n.startswith('hist__')]+['hist__'+n for n in h['auxiliaries']]
    cc=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    raw=dict(old,source=source,comparisons=pairs,auxiliaries=aux,history_packet=h,
        machine=machine,layout=h['layout'],tiles=len(h['maps']),operations=len(source),
        multiplications=cc['M'],additions_subtractions=cc['A'],equations=len(pairs),
        witnesses=len(aux),rule_order=machine['rule_order'],ordered_sparse=True)
    # The table changed, so this is a new raw composition. No same-map
    # identity guard or old selector/Pell tuple is repurposed.
    packet=prefix.units.rewrite(raw)
    packet.update(machine=machine,unit_product=True,ordered_sparse=True,
                  orientation_mode='oriented',rule_order=machine['rule_order'])
    return packet


def ledger(packet):
    return dict(parent.universal_ledger(packet),ordered_sparse=True)


def verify():
    rng=random.Random(808574);records=[];identities=words=frames=0;example=None
    for variant in ('sparse_tuned','balanced','tuned'):
        machine=ordered_table(variant);old=parent.universal_table()
        codes=parent.code_map(variant);h=history(variant)
        k=len(machine['copy_alphabet'])
        assert machine['tiles'][:k]==old['tiles'][:k] and len(machine['tiles'])==57
        for inline in (True,False):
            packet=build(inline_initial=inline,variant=variant);record=ledger(packet)
            records.append(record)
            identities+=parent.source_audit(packet,record,rng,24)
            if variant=='sparse_tuned' and inline:
                source,out=parent.polynomial_source(packet)
                example=dict(ledger=record,parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],
                    source=source,output=out,comparisons=packet['comparisons'],
                    tiles=machine['tiles'],rule_permutation=machine['parent_rule_permutation'],
                    history=planner.history_ledger(h),binary_prefix_code=codes)
        for _ in range(96):
            selection=[rng.randrange(57) for _ in range(rng.randrange(1,35))]
            translated=[machine['parent_tile_permutation'][j] for j in selection]
            images=parent.boundary.selected_images(machine['tiles'],selection)
            assert images==parent.boundary.selected_images(old['tiles'],translated)
            initial=rng.randrange(1,20);U,V=1,initial
            for j in selection:
                a,c,b,d=h['maps'][j];U,V=a*U+c,b*V+d
            assert U==prefix.sentinel(images[0],codes)
            assert V==initial*(1<<len(prefix.bits(images[1],codes)))+prefix.value(images[1],codes)
            assert prefix.decode(prefix.bits(images[0],codes),codes)==images[0]
            assert prefix.decode(prefix.bits(images[1],codes),codes)==images[1]
            words+=1
        for _ in range(48):
            q=rng.randrange(4,8);productions={(1,j):(j,2) for j in range(1,q+1)}
            params,left,right=parent.program_parameters(q,2,productions,q-1,q,variant)
            n=rng.randrange(2,20);x=rng.randrange(1,1<<n)
            blocks=parent.block_words(variant);physical=sum((blocks[int(bit)] for bit in bin(x)[2:].zfill(n)),())
            width=len(prefix.bits(blocks[0],codes));Q=1<<(width*n);R=(Q-1)//((1<<width)-1)
            c0,c1=(prefix.value(b,codes) for b in blocks)
            D=c0*R+(c1-c0)*parent.boundary.spread(x,width)
            Vi=(params['program_prefix']*Q+D)*params['program_suffix_scale']+params['program_suffix_value']
            initial=left+physical+right
            assert parent.bracket.valid(initial,machine) and Vi==prefix.sentinel(initial,codes)
            frames+=1
    assert example['ledger']['polynomial']==dict(operations=808,multiplications=349,additions_subtractions=459)
    assert example['ledger']['operations']==728 and example['ledger']['witnesses']==125
    assert example['ledger']['exact_degree']==130394
    rows=parent.local_derivations(ordered_table())
    return dict(status='PASS_GPCP_ORDERED_SPARSE_TM',ledgers=records,
        complete_source_identities=identities,signed_assignments=identities//2,
        arbitrary_word_permutation_and_append_cases=words,positive_input_frames=frames,
        local_rule_and_cleanup_rows=rows,example=example,
        scope='Same fixed universal machine and physical word relation by an explicit rule permutation; '
              'fresh complete selected histories and positive native extensions. All ordinary-input, '
              'padding and program-slice contracts inherited. No arithmetic optimality claim.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
    for rec in result['ledgers']:
        print(rec['code_variant'],rec['inline_initial'],rec['polynomial'],rec['exact_degree'])

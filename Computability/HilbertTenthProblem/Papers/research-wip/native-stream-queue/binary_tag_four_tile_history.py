"""Four continuing GPCP tiles for a fixed binary tag system.

The ordinary integer input is the sentinel of the encoded tag dataword.
No arbitrary-r.e.-set input compiler or numerical universal bound is claimed.
"""
import argparse
from collections import Counter
from itertools import product
import json
from pathlib import Path
import random

import gpcp_slope_class_compiler as planner
import pcp_uniform_affine_pair_units as units

execute=planner.execute
scalar=planner.scalar


def encode(word,beta):
    assert beta>=2 and set(word)<=set('bc')
    return ''.join('1'+'0'*beta+'1' if a=='b' else '1' for a in word)


def decode(word,beta):
    """Unique finite-word decoder; the final b-code bit is significant."""
    result=[];i=0
    while i<len(word):
        assert word[i]=='1'
        if i+1<len(word) and word[i+1]=='0':
            assert word[i:i+beta+2]=='1'+'0'*beta+'1'
            result.append('b');i+=beta+2
        else:
            result.append('c');i+=1
    return ''.join(result)


def endpoint(word,beta):
    assert word and word[-1]=='b'
    return encode(word[:-1],beta)+'1'+'0'*beta


def sentinel(word):return int('1'+word,2)


def tiles(beta,production):
    assert beta>=2 and production and production[-1]=='b'
    assert set(production)<=set('bc')
    b=encode('b',beta)
    return (('1','1'+encode(production[:-1],beta)+'10'),
            (b,'110'),(b,'0'),('1','0'))


def images(table,selection):
    return tuple(''.join(table[i][side] for i in selection) for side in (0,1))


def is_match(beta,production,word,selection):
    a,b=images(tiles(beta,production),selection)
    return a+'1'+'0'*beta==endpoint(word,beta)+b


def tag_step(word,beta,production):
    assert len(word)>=beta
    return word[beta:]+('b' if word[0]=='b' else production)


def encode_halting_trace(word,beta,production,limit=100):
    initial=word;selection=[];steps=0
    while len(word)>=beta and steps<limit and len(word)<10000:
        selection.append(1 if word[0]=='b' else 0)
        selection.extend(2 if a=='b' else 3 for a in word[1:beta])
        word=tag_step(word,beta,production);steps+=1
    if word=='b':
        assert is_match(beta,production,initial,selection)
        return tuple(selection),steps
    return None


def decode_solution(word,beta,production,selection):
    assert is_match(beta,production,word,selection)
    assert len(selection)%beta==0
    for at in range(0,len(selection),beta):
        block=selection[at:at+beta]
        assert block[0] in (0,1) and all(i in (2,3) for i in block[1:])
        if len(word)<beta:return word
        read=''.join('b' if i in (1,2) else 'c' for i in block)
        assert read==word[:beta]
        word=tag_step(word,beta,production)
    assert word=='b'
    return word


def affine_maps(beta,production):
    return tuple((1<<len(a),int(a,2),1<<len(b),int(b,2))
                 for a,b in tiles(beta,production))


def build(beta=3,production='ccbbb'):
    h=planner.choose_history(affine_maps(beta,production))
    aliases={'Vinitial':'x','Vfinal':'tag_terminal'}
    alias=lambda a:aliases.get(a,a)
    front=[('tag_terminal_scale','*',1<<(beta+1),'Ufinal'),
           ('tag_terminal','+','tag_terminal_scale',1<<beta)]
    source=front+[(n,op,alias(a),alias(b)) for n,op,a,b in h['source']]
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    raw=dict(h,parameters=['x'],auxiliaries=['Ufinal']+h['auxiliaries'],
             source=source,comparisons=[(alias(a),alias(b)) for a,b in h['comparisons']],
             operations=len(source),multiplications=counts['M'],
             additions_subtractions=counts['A'],witnesses=h['witnesses']+1,
             beta=beta,production=production,history_packet=h)
    packet=units.rewrite(raw)
    N=packet['scale_exponent']
    packet.update(raw_packet=raw,exact_degree=58*N+28,
                  alternative_SOS_degree=84*N+16)
    return packet


def polynomial_source(packet,include_empty=True):
    source,out=units.polynomial_source(packet)
    if include_empty:
        source += [('tag_initial_singleton','-','x',sentinel(endpoint('b',packet['beta']))),
                   ('tag_complete_output','*',out,'tag_initial_singleton')]
        out='tag_complete_output'
    return source,out


def ledger(packet):
    result=units.ledger(packet)
    result.update(beta=packet['beta'],production=packet['production'],
                  history=planner.history_ledger(packet['history_packet']))
    for flag,name in [(False,'nonempty'),(True,'including_initial_singleton')]:
        source,_=polynomial_source(packet,flag)
        cc=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
        result[name]=dict(operations=len(source),multiplications=cc['M'],
                         additions_subtractions=cc['A'],degree=packet['exact_degree']+flag)
    return result


def verify():
    rng=random.Random(4195666);records=[];identities=frames=traces=decodings=0
    examples=[(2,'cbb'),(3,'ccbbb'),(4,'ccbbbbb'),(10,'cbcbbbbbbb')]
    for beta,production in examples:
        assert (len(production)-1)%(beta-1)==0
        packet=build(beta,production);records.append(ledger(packet))
        raw=packet['raw_packet'];h=packet['history_packet']
        assert h['operations']==161 and h['scale_exponent']==11
        assert packet['operations']==166 and packet['equations']==10 and packet['witnesses']==28
        assert ledger(packet)['nonempty']==dict(operations=195,multiplications=91,
                                               additions_subtractions=104,degree=666)
        for case in range(64):
            values={n:rng.randrange(1,6) if case<48 else rng.randrange(-3,4)
                    for n in packet['parameters']+packet['auxiliaries']}
            if case<48:values[packet['root_coordinate']]=2*rng.randrange(1,5)+1
            units.audit_identity(raw,packet,values)
            new=execute(packet['source'],values)
            assert new['tag_terminal']==(1<<(beta+1))*values['Ufinal']+(1<<beta)
            source,out=polynomial_source(packet,True)
            base,baseout=polynomial_source(packet,False)
            assert execute(source,values)[out]==execute(base,values)[baseout]*(values['x']-sentinel(endpoint('b',beta)))
            identities+=1
        for _ in range(96):
            word=''.join(rng.choice('bc') for _ in range(rng.randrange(1,20)))+'b'
            assert decode(encode(word,beta),beta)==word;decodings+=1
            selection=tuple(rng.randrange(4) for _ in range(rng.randrange(1,12)))
            uv=[1,sentinel(endpoint(word,beta))]
            for index in selection:
                a,c,b,d=h['maps'][index];uv=[a*uv[0]+c,b*uv[1]+d]
            upper,lower=images(tiles(beta,production),selection)
            assert uv==[sentinel(upper),sentinel(endpoint(word,beta)+lower)]
            assert ((1<<(beta+1))*uv[0]+(1<<beta)==uv[1])==is_match(beta,production,word,selection)
            frames+=1
        for length in range(1,10):
            if (length-1)%(beta-1):continue
            for prefix in product('bc',repeat=length-1):
                word=''.join(prefix)+'b'
                result=encode_halting_trace(word,beta,production)
                if result is not None:
                    selection,_=result
                    assert decode_solution(word,beta,production,selection)=='b';traces+=1
    # Exhaust all short tile words, including choices not respecting tag phases.
    matches=checked=0
    for beta,production,maxlength in [(2,'cbb',8),(3,'ccbbb',6),(4,'ccbbbbb',5)]:
        table=tiles(beta,production)
        inputs=['b','b'*beta,'c'*(beta-1)+'b','b'*(beta+1),'cbcbb']
        for length in range(maxlength+1):
            for selection in product(range(4),repeat=length):
                upper,lower=images(table,selection)
                for word in inputs:
                    checked+=1
                    if upper+'1'+'0'*beta==endpoint(word,beta)+lower:
                        decode_solution(word,beta,production,selection);matches+=1
    # The congruence is a real completeness condition: cc stops immediately
    # at beta=3 but violates both the final-b and length hypotheses. bb ends
    # in b yet stops at length2, so cannot reach the fixed final singleton.
    assert len('bb')<3 and len('bb')%(3-1)!=1
    assert not any(is_match(3,'ccbbb','bb',s) for n in range(7)
                   for s in product(range(4),repeat=n))
    # A matching equation may consume future appended letters after the
    # genuine queue has already halted. The converse must stop there.
    assert is_match(3,'cb','cb',(0,2,3))
    assert decode_solution('cb',3,'cb',(0,2,3))=='cb'
    sample=build();degree=units.degree_audit(sample)
    src,out=polynomial_source(sample,True)
    return dict(status='PASS_BINARY_TAG_FOUR_TILE_HISTORY',ledgers=records,
        degree_audit=degree,example=dict(parameters=sample['parameters'],
            auxiliaries=sample['auxiliaries'],source=src,output=out,
            comparisons=sample['comparisons'],tiles=tiles(3,'ccbbb')),
        checks=dict(full_signed_unit_source_identities=identities,
            independent_affine_string_boundaries=frames,injective_decodings=decodings,
            halting_trace_roundtrips=traces,arbitrary_tile_word_checks=checked,
            arbitrary_tile_word_matches=matches,full_Pell_witnesses_materialized=False),
        scope='Four fixed continuing tiles and fully paid integer-sentinel input predicate. '
              'No ordinary-input compiler into a fixed universal tag system is claimed.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])

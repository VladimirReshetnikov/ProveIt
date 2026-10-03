"""Exact U9 -> clockwise -> CTS/tag metadata and paired ordinary-input cut.

This packet does not build a new universal polynomial. It supplies an exact
fixed table, width, checked power chain, and positive input-format contracts.
Neither the fixed production u nor any integer with D bits is materialized.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import ordinary_tm_clockwise_compiler as cw
import neary_woods_explicit_universal_tm as published
import neary_woods_u15_tag_metadata as metadata

D_EXPECTED=47946621298704238734708993009920
# A fixed list of exponents; each is checked to be a sum of prior exponents.
# This is a finite power schedule, not a minimal-chain claim.
POWER_EXPONENTS=(
    2,3,6,9,
    15,17,21,23,
    27,29,30,31,
    60,120,121,242,
    484,968,1936,3872,
    7744,15488,30976,61952,
    61969,123938,247876,495752,
    991504,1983008,1983025,3966050,
    7932100,7932103,15864206,31728412,
    63456824,126913648,253827296,507654592,
    1015309184,2030618368,2030618397,4061236794,
    8122473588,16244947176,32489894352,64979788704,
    64979788719,129959577438,259919154876,519838309752,
    1039676619504,2079353239008,4158706478016,8317412956032,
    8317412956063,16634825912126,33269651824252,66539303648504,
    133078607297008,266157214594016,532314429188032,1064628858376064,
    1064628858376087,2129257716752174,4258515433504348,8517030867008696,
    17034061734017392,34068123468034784,68136246936069568,68136246936069595,
    136272493872139190,272544987744278380,545089975488556760,1090179950977113520,
    2180359901954227040,4360719803908454080,8721439607816908160,17442879215633816320,
    34885758431267632640,69771516862535265280,139543033725070530560,139543033725070530591,
    279086067450141061182,279086067450141061183,558172134900282122366,1116344269800564244732,
    2232688539601128489464,4465377079202256978928,8930754158404513957856,17861508316809027915712,
    35723016633618055831424,71446033267236111662848,142892066534472223325696,285784133068944446651392,
    571568266137888893302784,1143136532275777786605568,2286273064551555573211136,2286273064551555573211145,
    4572546129103111146422290,9145092258206222292844580,18290184516412444585689160,36580369032824889171378320,
    73160738065649778342756640,146321476131299556685513280,292642952262599113371026560,585285904525198226742053120,
    585285904525198226742053137,1170571809050396453484106274,2341143618100792906968212548,4682287236201585813936425096,
    9364574472403171627872850192,18729148944806343255745700384,37458297889612686511491400768,37458297889612686511491400789,
    74916595779225373022982801578,149833191558450746045965603156,187291489448063432557457003945,374582978896126865114914007890,
    749165957792253730229828015780,1498331915584507460459656031560,2996663831169014920919312063120,5993327662338029841838624126240,
    11986655324676059683677248252480,23973310649352119367354496504960,47946621298704238734708993009920,
 )


@lru_cache(None)
def compiled_u9():
    rename={'c':'_','b':'0','d':'1'}
    delta={(q,rename[read]):(rename[write],move,target)
           for (q,read),(target,write,move) in published.transition_table('9,3',True).items()}
    machine=cw.compile_tm(tuple(f'u{i}' for i in range(1,10))+('halt',),
                          ('0','1','_'),delta,'u1','halt')
    binary=cw.binary.binary_compile(machine['alphabet'],machine['transitions'],('run','u1'),cw.HALT)
    nonhalt={q for q,_ in binary['transitions']}
    ordered=[binary['start']]+sorted(nonhalt-{binary['start']},key=repr)+[binary['halt']]
    labels={q:i+1 for i,q in enumerate(ordered)}
    rules={(labels[q],bit):(write,labels[target]) for (q,bit),(write,target) in binary['transitions'].items()}
    assert labels[binary['start']]==1 and labels[binary['halt']]==len(ordered)
    return machine,binary,rules


def power_chain():
    available={1};rows=[]
    for exponent in POWER_EXPONENTS:
        assert exponent>max(available)
        pairs=[(a,exponent-a) for a in sorted(available)
               if a<=exponent-a and exponent-a in available]
        assert pairs,('not an addition-chain exponent',exponent)
        a,b=pairs[0];rows.append((exponent,a,b));available.add(exponent)
    assert len(rows)==127 and rows[-1][0]==D_EXPECTED
    return tuple(rows)


def bit_blocks():
    a1=published.a_code(1,'9,3');a3=published.a_code(3,'9,3')
    return a3+a1,a1+a3


def physical_input_fixture(q,h,productions,x,padding_rounds=0):
    """Full original-head cut; every n is padded independently of the program."""
    assert q>=5 and h>=2 and x>0 and padding_rounds>=0
    machine,binary,_=compiled_u9();codes=binary['codes'];a=binary['a']
    right,left=q-1,q
    assert right not in (1,3) and left not in (1,3)
    program=published.bts_program(q,h,productions,'9,3')
    fixed=a*(len(program)+4*(q+right+left)+2)
    bound=(fixed+63)//64
    n=(1<<(max(2,bound+1,x.bit_length())-1).bit_length())<<padding_rounds
    bits=format(x,f'0{n}b')
    data=[('e',1)]
    for bit in bits:data.extend((('a',3),('a',1)) if bit=='0' else (('a',1),('a',3)))
    data.extend((('a',right),('a',left)))
    contents,head=published.encoded_configuration(q,h,productions,data,'9,3')
    rename=lambda char:('data',{'c':'_','b':'0','d':'1'}[char])
    entire=(cw.LEFT,)+tuple(map(rename,contents))+(cw.RIGHT,)
    cut=entire[head+1:]+entire[:head+1]
    assert cut[0]==rename('b') and contents[:head]==program
    coded=lambda w:''.join(codes[rename(c)] for c in w)
    prefix=coded('b'*(4*q))
    block0,block1=map(coded,bit_blocks())
    middle=coded(published.a_code(right,'9,3')+published.a_code(left,'9,3'))
    middle+=codes[cw.RIGHT]+codes[cw.LEFT]+coded(program)
    got=''.join(codes[c] for c in cut)
    assert got==prefix+''.join(block1 if bit=='1' else block0 for bit in bits)+middle
    assert len(block0)==len(block1)==64 and block1>block0
    assert Counter(block0)==Counter(block1)==Counter({'0':62,'1':2})
    assert len(prefix)+len(middle)==fixed and len(got)==64*n+fixed
    assert n>bound and (1<<(len(got)-1).bit_length())==128*n
    assert sum(kind=='a' for kind,_ in data)==2*n+2>=6
    # The source checkpoint is the same original U9 cell at the published cut.
    q0,tape,position=cw.decode_checkpoint(machine,('run','u1'),cut)
    assert q0=='u1' and position==head
    assert ''.join({'_':'c','0':'b','1':'d'}[c] for c in tape)==contents
    return dict(BTS_symbols=q,BTS_states=h,program_tape_symbols=len(program),
                fixed_binary_overhead=fixed,positive_program_bound=bound,
                padded_duration=n,input=x,initial_binary_cells=len(got),counter=128*n,
                physical_word_sha256=hashlib.sha256(got.encode()).hexdigest())


def published_simulations():
    """Finite table checks supplement, and do not prove, the imported simulation."""
    result=[]
    for h,word,arity in ((2,'01',1),(2,'10',2),(3,'01',1),(3,'10',2)):
        q=5
        productions={(j,i):((i,) if arity==1 else (i,i))+(j+1,)
                     for j in range(1,h) for i in range(1,q+1)}
        data=[('e',1)]
        for bit in word:data.extend((('a',3),('a',1)) if bit=='0' else (('a',1),('a',3)))
        data.extend((('a',4),('a',5)))
        contents,head=published.encoded_configuration(q,h,productions,data,'9,3')
        got=published.simulate(contents,head,'9,3',limit=6000000)
        assert got['halted'] and (got['state'],got['read'])==('u5','b'),got
        result.append(dict(q=q,h=h,word=word,output_arity=arity,**got))
    # Preserve the known bad one-A boundary instead of using a timeout as evidence.
    prod={(1,i):(i,2) for i in (1,2)}
    contents,head=published.encoded_configuration(2,2,prod,[('e',1),('a',1)],'9,3')
    escape=published.simulate(contents,head,'9,3',limit=10000)
    assert escape.get('proved_right_escape') and not escape['halted']
    return result,escape


def verify():
    machine,binary,rules=compiled_u9();ledger=cw.ledger(machine,binary)
    assert ledger['binary_states']==1968 and ledger['clockwise_states']==49
    assert ledger['distinct_clockwise_output_target_pairs']==226
    # Every renamed source instruction, including the sole accepting adapter.
    rename={'c':'_','b':'0','d':'1'}
    for (q,read),(target,write,move) in published.transition_table('9,3',True).items():
        assert machine['source_total'][q,rename[read]]==(rename[write],move,target)
    table=metadata.cts_table(ledger['binary_states'],rules);summary=metadata.row_summary(table)
    counts=metadata.track_counts(table['p'],table['total_length'],summary['maximum'])
    E2=len({(w,q) for w,q in machine['transitions'].values() if len(w)==2})
    assert E2==18 and table['T2']==4*E2==72
    D=128*table['z']*counts['bit_block_length'];assert D==D_EXPECTED
    chain=power_chain();rng=random.Random(93042026);modular=0
    for _ in range(64):
        modulus=rng.randrange(2,1<<24);base=rng.randrange(-modulus,modulus)
        vals={1:base%modulus}
        for e,a,b in chain:vals[e]=(vals[a]*vals[b])%modulus
        assert vals[D]==pow(base,D,modulus);modular+=1
    frames=[]
    for q in range(5,8):
        for h in (2,3):
            for case in range(4):
                productions={(j,i):tuple(rng.randrange(1,q+1) for _ in range(rng.randrange(1,3)))+(h,)
                             for j in range(1,h) for i in range(1,q+1)}
                x=rng.randrange(1,256)
                for padding in (0,1):frames.append(physical_input_fixture(q,h,productions,x,padding))
    simulation,escape=published_simulations()
    return dict(status='PASS_NEARY_WOODS_U9_TAG_METADATA',ordinary_clockwise_binary=ledger,
                initial_length_scope='The inherited raw-bit ledger a=4,b=8 is not this U9 frame: actual tape length is 64*n+b_S, b_S=4*(len(program)+4*(q_B+right_index+left_index)+2).',
                binary_start='read(run(u1),empty_prefix)',source_renaming_checks=27,
                input_A_indices=dict(zero=[3,1],one=[1,3]),
                two_cell_clockwise_output_pairs=E2,binary_two_cell_instructions=table['T2'],
                cts=summary,tag_counts=counts,data_physical_bit_width=64,data_binary_width=D,
                width_bit_length=D.bit_length(),width_population=D.bit_count(),
                binary_power_chain_multiplications=D.bit_length()+D.bit_count()-2,
                fixed_power_chain_multiplications=len(chain),
                fixed_power_chain_sha256=hashlib.sha256(json.dumps(chain,separators=(',',':')).encode()).hexdigest(),
                modular_chain_checks=modular,actual_U9_physical_frame_checks=len(frames),
                physical_frame_examples=frames[:4],published_simulation_checks=simulation,
                scoped_singleton_escape=escape,
                scope='Exact fixed U9-derived table, paired-input family, tag width and power schedule. No expanded tag production, numeral 2^D, or composed universal arithmetic operation bound is claimed.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])

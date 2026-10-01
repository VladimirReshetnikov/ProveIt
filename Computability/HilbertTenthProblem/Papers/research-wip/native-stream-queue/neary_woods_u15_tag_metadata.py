"""Exact finite U15 -> binary clockwise -> CTS -> tag size metadata.

Actual CTS appendants are sparse bit words. No universal u, G_i, DATA_i,
or integer 2^D is materialized. Fixed program boundary values remain symbolic.
"""
import argparse
from collections import Counter,deque
from dataclasses import dataclass
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import ordinary_tm_clockwise_compiler as cw
import neary_woods_explicit_universal_tm as published
import binary_tag_fixed_halt_bridge as tag


@dataclass(frozen=True)
class Word:
    length:int
    ones:tuple=()

    def __post_init__(self):
        assert self.length>=0 and tuple(sorted(set(self.ones)))==self.ones
        assert all(0<=i<self.length for i in self.ones)

    def __add__(self,other):
        return Word(self.length+other.length,self.ones+tuple(self.length+i for i in other.ones))

    def literal(self):
        assert self.length<10000,'Only small independent fixtures may be materialized.'
        bits=['0']*self.length
        for i in self.ones:bits[i]='1'
        return ''.join(bits)


def zeros(n):return Word(n)
def one(n,i):return Word(n,(i,))


@lru_cache(None)
def compiled_u15():
    rename={'c':'0','b':'1'}
    delta={(q,rename[read]):(rename[write],move,target)
           for (q,read),(target,write,move) in published.transition_table('15,2',True).items()}
    # An exterior blank and a stored c have identical read behavior.
    for i in range(1,16):delta[f'u{i}','_']=delta[f'u{i}','0']
    machine=cw.compile_tm(tuple(f'u{i}' for i in range(1,16))+('halt',),
                          ('0','1','_'),delta,'u1','halt')
    binary=cw.binary.binary_compile(machine['alphabet'],machine['transitions'],('run','u1'),cw.HALT)
    nonhalt={q for q,_ in binary['transitions']}
    ordered=[binary['start']]+sorted(nonhalt-{binary['start']},key=repr)+[binary['halt']]
    labels={q:i+1 for i,q in enumerate(ordered)}
    rules={(labels[q],bit):(write,labels[target]) for (q,bit),(write,target) in binary['transitions'].items()}
    assert labels[binary['start']]==1 and labels[binary['halt']]==len(ordered)
    return machine,binary,rules


def cts_table(Q,rules):
    """Literal primary row templates; unspecified appendants are empty.

    Generic state/control rows use i<Q. Counter state copies include Q;
    the unique halt activation h has its separate self-copying appendant.
    """
    assert Q>=2 and set(rules)=={(i,b) for i in range(1,Q) for b in '01'}
    assert all(len(w) in (1,2) and set(w)<=set('01') and 1<=j<=Q for w,j in rules.values())
    z=30*Q+61;p=2*z;rows={};families={}
    def put(index,word,family):
        assert 0<=index<p and index not in rows,('index collision',index)
        rows[index]=word;families[index]=family
    tape={'0':one(p,1),'1':one(p,2)}
    marked={'0':one(p,3),'1':one(p,4)}
    mu=one(z,0);slash=one(p,5);prime=one(p,6)
    state=lambda i:one(p,30*i+20)
    flag=lambda i:one(p,30*i+25)
    for b in (0,z):
        for j,obj in enumerate((slash if b==0 else prime,tape['0'],tape['1'],marked['0'],marked['1'],slash,prime)):
            put(b+j,obj,'fixed_stage1')
        objects=(one(z,7),one(z,8),marked['0'],marked['1'],slash,prime) if b==0 else (tape['0'],tape['1'],marked['0'],marked['1'],slash,prime)
        for j,obj in enumerate(objects,11):put(b+j,obj,'fixed_test')
        objects=(marked['0'],marked['1'],slash,mu,tape['0'] if b==0 else marked['0'],tape['1'] if b==0 else marked['1'])
        for j,obj in enumerate(objects,23):put(b+j,obj,'fixed_stage2')
    D=one(p+40,39)
    for i in range(1,Q):
        base=30*i
        s1p=one(p+10,base+21);s1pf=one(p+10,base+26)
        for index,obj in ((base+20,s1p),(z+base+20,zeros(z)+s1pf),
                          (base+25,s1pf),(z+base+25,zeros(z)+s1pf)):
            put(index,obj,'state_stage1')
        for index,obj in ((base+21,one(p+10,base+12)),
                          (z+base+21,one(z+base+20,base+14)),
                          (base+26,one(p+10,base+17)),
                          (z+base+26,one(z+base+30,base+19))):
            put(index,obj,'state_test')
        put(base+22,zeros(p-20)+state(i),'state_stage2')
        put(base+27,zeros(p-20)+flag(i),'state_stage2')
        put(z+base+24,zeros(p-base-30),'state_stage3')
        put(z+base+29,zeros(p-base-40),'state_stage3')
        for bit in '01':
            write,target=rules[i,bit];out=Word(0)
            for char in write:out=out+tape[char]
            out=out+state(target)
            put(base+31+int(bit),(D+out) if len(write)==2 else out,'transition')
            put(base+41+int(bit),out,'transition')
        for offset in (33,43):
            for j,obj in enumerate((tape['0'],tape['1'],mu)):put(base+offset+j,obj,'state_passive')
    for index,obj in ((39,zeros(p-40)),(40,mu+mu),(z+40,mu+mu),(41,tape['0']),(42,tape['1'])):
        put(index,obj,'fixed_counter')
    for i in range(1,Q+1):put(30*i+60,state(i),'counter_state_copy')
    h=30*Q+20;put(h,state(Q),'halt')
    T2=sum(len(w)==2 for w,_ in rules.values())
    length=sum(w.length for w in rows.values());ones=sum(len(w.ones) for w in rows.values())
    assert length==(56*Q+30)*z-40+(6*z+40)*T2
    assert ones==25*Q+21+3*T2
    assert len(rows)==23*Q+22 and p-len(rows)==37*Q+100
    assert max(w.length for w in rows.values())==(8*z+40 if T2 else 4*z)
    assert rows[0].length==rows[h].length==p
    return dict(Q=Q,z=z,p=p,halt=h,T2=T2,rows=rows,families=families,
                total_length=length,total_ones=ones)


def track_counts(p,total_length,maximum):
    beta=10*p;modulus=beta-1;minimum=11*max(p,maximum)+3
    s=minimum+(1-minimum)%modulus
    # alpha0 is nonempty and alpha_h has length p for the actual CTS tables.
    b=6*p*s+20*p*p-2+10*(total_length-p);c=beta*s-b
    assert b>0 and c>0 and s>=minimum and s%modulus==1
    eu=(beta+2)*b+c;k=(-11)%modulus
    assert k==beta-12
    K=(k+1)*eu+10*(beta+2)
    return dict(beta=beta,s=s,minimum_track_length=minimum,u_b=b,u_c=c,u_length=beta*s,
                e_u_length=eu,padding_u_copies=k,bit_block_length=K)


def row_summary(table):
    rows=table['rows'];families=table['families'];summary={}
    for family in sorted(set(families.values())):
        words=[w for i,w in rows.items() if families[i]==family]
        summary[family]=dict(rows=len(words),length=sum(w.length for w in words),ones=sum(len(w.ones) for w in words))
    wire=[[i,w.length,w.ones] for i,w in sorted(rows.items())]
    return dict(nonempty_appendants=len(rows),empty_appendants=table['p']-len(rows),
                maximum=max(w.length for w in rows.values()),total_length=table['total_length'],
                total_ones=table['total_ones'],row_families=summary,
                sparse_table_sha256=hashlib.sha256(json.dumps(wire,separators=(',',':')).encode()).hexdigest())


def one_step_cts_fixture(tape,write):
    """A small literal CTS run to the first accepting activation.

    Passive counter objects can lie between tape objects after a transition.
    Decode their types instead of assuming the initial contiguous layout.
    """
    Q=2;rules={(1,b):(write,2) for b in '01'};table=cts_table(Q,rules)
    z=table['z'];p=table['p'];state=lambda i:one(p,30*i+20).literal()
    cell=lambda b:one(p,1+int(b)).literal();mu=one(z,0).literal()
    counter=1<<(len(tape)-1).bit_length()
    initial=state(1)+''.join(cell(b) for b in tape)+mu*counter
    expected_tape=tape[1:]+write;nextcounter=1<<(len(expected_tape)-1).bit_length()
    appendants={i:w.literal() for i,w in table['rows'].items()}
    queue=deque(initial);marker=0;steps=0
    while steps<2000000:
        if marker==table['halt'] and queue[0]=='1':
            full='0'*table['halt']+''.join(queue)
            assert full.startswith(state(2))
            j=p;decoded='';count=0
            while j<len(full):
                if full[j]=='1':
                    assert full[j:j+z]==mu;j+=z;count+=1
                else:
                    if full[j:j+p]==cell('0'):decoded+='0'
                    else:assert full[j:j+p]==cell('1');decoded+='1'
                    j+=p
            assert decoded==expected_tape and count==nextcounter
            return steps
        assert queue,'premature empty word'
        bit=queue.popleft()
        if bit=='1':queue.extend(appendants.get(marker,''))
        marker=(marker+1)%p;steps+=1
    raise AssertionError(('CTS run did not reach the exact one-step configuration',tape,write))


def physical_input_fixture(q,h,productions,x):
    """Check the actual published head cut, before expanding any CTS objects."""
    machine,binary,_=compiled_u15();codes=binary['codes'];a=binary['a']
    right,left=q-1,q
    program=published.bts_program(q,h,productions)
    b_program=a*(len(program)+16*(q+right+left)-12)
    bound=(b_program+127)//128
    n=1<<(max(2,bound+1,x.bit_length())-1).bit_length()
    bits=format(x,f'0{n}b')
    data=[('e',1)]
    for bit in bits:data.extend((('a',2),('a',1)) if bit=='0' else (('a',1),('a',2)))
    data.extend((('a',right),('a',left)))
    contents,head=published.encoded_configuration(q,h,productions,data)
    rename=lambda char:('data','0' if char=='c' else '1')
    entire=(cw.LEFT,)+tuple(map(rename,contents))+(cw.RIGHT,)
    cut=entire[head+1:]+entire[:head+1]
    assert cut[0]==rename('c') and contents[:head]==program+'b'
    coded=lambda w:''.join(codes[rename(c)] for c in w)
    prefix=coded('c'+'cb'*(8*q))
    block0,block1=map(coded,published.bit_blocks())
    middle=coded(published.a_code(right)+published.a_code(left))+codes[cw.RIGHT]+codes[cw.LEFT]+coded(program+'b')
    got=''.join(codes[c] for c in cut)
    assert got==prefix+''.join(block1 if bit=='1' else block0 for bit in bits)+middle
    assert len(block0)==len(block1)==128 and block1>block0
    assert Counter(block0)==Counter(block1)
    assert len(prefix)+len(middle)==b_program and len(got)==128*n+b_program
    assert n>bound and (1<<(len(got)-1).bit_length())==256*n
    return dict(BTS_symbols=q,BTS_states=h,program_tape_symbols=len(program),
                fixed_binary_overhead=b_program,positive_program_bound=bound,
                padded_duration=n,input=x,initial_binary_cells=len(got),counter=256*n,
                physical_word_sha256=hashlib.sha256(got.encode()).hexdigest())


def verify():
    machine,binary,rules=compiled_u15();ledger=cw.ledger(machine,binary);Q=ledger['binary_states']
    table=cts_table(Q,rules);summary=row_summary(table)
    counts=track_counts(table['p'],table['total_length'],summary['maximum'])
    E2=len({(w,q) for w,q in machine['transitions'].values() if len(w)==2})
    assert table['T2']==ledger['binary_block_width']*E2==128
    assert Q==3089 and ledger['clockwise_states']==78
    D=256*table['z']*counts['bit_block_length'];muD=D.bit_length()+D.bit_count()-2
    rng=random.Random(15022026);small_rows=0
    for q in range(2,14):
        for kind in ('one','two','mixed'):
            rr={(i,b):(''.join(rng.choice('01') for _ in range(1 if kind=='one' else 2 if kind=='two' else rng.randrange(1,3))),rng.randrange(1,q+1))
                for i in range(1,q) for b in '01'}
            small=cts_table(q,rr);small_rows+=len(small['rows'])
            # Independent literal materialization of only the small appendants.
            assert sum(len(w.literal()) for w in small['rows'].values())==small['total_length']
            assert sum(w.literal().count('1') for w in small['rows'].values())==small['total_ones']
    tracks=0
    for p in range(2,10):
        for case in range(4):
            alphas=[''.join(rng.choice('01') for _ in range(p if i in (0,p-1) else rng.randrange(8))) for i in range(p)]
            packet=tag.build_tracks(alphas,p-1);u=tag.materialize(packet)
            got=track_counts(p,sum(map(len,alphas)),max(map(len,alphas)))
            assert (got['s'],got['u_b'],got['u_c'])==(packet['s'],u.count('b'),u.count('c'))
            for b in '01':
                block=tag.objects(u)[b]+u*packet['padding_u_copies']
                assert block.count('b')*(packet['beta']+2)+block.count('c')==got['bit_block_length']
            tracks+=1
    cts_steps=[]
    for tape in ('00','01','101','0110'):
        for write in ('0','1','01','10'):cts_steps.append(one_step_cts_fixture(tape,write))
    frames=[]
    for q in range(4,7):
        for h in (2,3):
            for case in range(4):
                productions={(j,i):tuple(rng.randrange(1,q+1) for _ in range(rng.randrange(1,3)))+(h,)
                             for j in range(1,h) for i in range(1,q+1)}
                frames.append(physical_input_fixture(q,h,productions,rng.randrange(1,128)))
    return dict(status='PASS_NEARY_WOODS_U15_TAG_METADATA',ordinary_clockwise_binary=ledger,
                initial_length_scope='The inherited ledger a=4,b=8 describes raw ordinary bits. Actual framed U15 input has 128*n+b_S cells, b_S=4*(len(program)+16*(q_B+right_index+left_index)-12).',
                binary_start='read(run(u1),empty_prefix)',two_cell_clockwise_output_pairs=E2,
                binary_two_cell_instructions=table['T2'],cts=summary,tag_counts=counts,
                data_physical_bit_width=128,data_binary_width=D,width_bit_length=D.bit_length(),
                width_population=D.bit_count(),binary_power_chain_multiplications=muD,
                small_symbolic_tables=36,small_rows_materialized=small_rows,
                literal_track_population_checks=tracks,full_small_cts_steps=len(cts_steps),
                small_cts_step_counts=cts_steps,
                actual_U15_physical_frame_checks=len(frames),physical_frame_examples=frames[:4],
                scope='Exact fixed U15-derived table metadata and symbolic tag sizes. No universal tag word or numeral 2^D is materialized; no composed universal arithmetic count is claimed.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])

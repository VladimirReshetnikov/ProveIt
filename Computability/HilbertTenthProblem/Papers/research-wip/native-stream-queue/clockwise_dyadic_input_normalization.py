"""Fixed binary clockwise input blocks and exact counter-scale reuse.

The emitted binary transition table is explicit. This is a machine/input
normalization theorem, not a complete Diophantine compiler or its cost.
"""
import argparse
from collections import deque
import hashlib
import json
from pathlib import Path
import random


def block_codes(alphabet,a=None):
    alphabet=tuple(alphabet)
    assert alphabet and len(set(alphabet))==len(alphabet)
    needed=max(2,1+(len(alphabet)-1).bit_length())
    if a is None:a=1<<(needed-1).bit_length()
    assert a>=needed and a&(a-1)==0
    return {symbol:'0'+format(i,f'0{a-1}b') for i,symbol in enumerate(alphabet)}


def binary_compile(alphabet,transitions,start,halt,a=None):
    """Rules are (state,symbol)->(nonempty write tuple,next state).

    A clockwise step advances past its entire one/two-symbol replacement.
    All nonhalting emitted states have both binary instructions.
    """
    alphabet=tuple(alphabet);codes=block_codes(alphabet,a);a=len(next(iter(codes.values())))
    assert start!=halt
    decode={code:symbol for symbol,code in codes.items()}
    states={start,halt}
    for (q,read),(write,target) in transitions.items():
        assert q!=halt and read in codes and len(write) in (1,2)
        assert all(s in codes for s in write);states.update((q,target))
    trap=('trap',);end=('halt',);initial=('read',start,'')
    roots=[('read',q,'') for q in sorted(states,key=repr) if q!=halt]+[trap]
    pending=deque(roots);seen=set();rules={}
    while pending:
        state=pending.popleft()
        if state==end or state in seen:continue
        seen.add(state)
        for bit in '01':
            mode=state[0]
            if mode=='trap':write,next_state=bit,trap
            elif mode=='read':
                _,q,prefix=state;j=len(prefix)
                write='1' if j==0 else '0'
                got=prefix+bit
                if j==0 and bit!='0':next_state=trap
                elif len(got)<a:next_state=('read',q,got)
                elif got not in decode or (q,decode[got]) not in transitions:next_state=trap
                else:
                    output,target=transitions[q,decode[got]]
                    encoded=''.join(codes[s] for s in output)
                    next_state=('seek',target,encoded,0)
            elif mode=='seek':
                _,q,output,j=state
                if j==0 and bit=='1':
                    size=len(output)//a;write=output[:size]
                    next_state=('emit',q,output,1)
                else:write,next_state=bit,('seek',q,output,(j+1)%a)
            else:
                assert mode=='emit'
                _,q,output,j=state;size=len(output)//a
                if bit!='0':write,next_state=bit,trap
                else:
                    write=output[size*j:size*(j+1)]
                    next_state=(end if q==halt else ('read',q,'')) if j==a-1 else ('emit',q,output,j+1)
            assert len(write) in (1,2) and set(write)<=set('01')
            rules[state,bit]=(write,next_state)
            if next_state not in seen and next_state!=end:pending.append(next_state)
    assert all((q,b) in rules for q in seen for b in '01')
    return dict(alphabet=alphabet,codes=codes,a=a,marker='1'+'0'*(a-1),
                transitions=rules,start=initial,halt=end,trap=trap,
                logical_start=start,logical_halt=halt,logical_transitions=transitions)


def binary_step(machine,state,word):
    assert word and state!=machine['halt']
    write,target=machine['transitions'][state,word[0]]
    return target,word[1:]+write


def macro(machine,state,word):
    """Replay actual binary instructions until the next logical checkpoint."""
    assert state!=machine['logical_halt'] and word
    codes=machine['codes'];data=''.join(codes[s] for s in word)
    current=('read',state,'');initial_cells=len(word);steps=0
    while True:
        current,data=binary_step(machine,current,data);steps+=1
        assert steps<=machine['a']*(initial_cells+1)
        if current==machine['halt'] or (current[0]=='read' and current[2]==''):break
    write,target=machine['logical_transitions'][state,word[0]]
    expected=word[1:]+tuple(write)
    assert data==''.join(codes[s] for s in expected)
    assert current==(machine['halt'] if target==machine['logical_halt'] else ('read',target,''))
    assert steps==machine['a']*(initial_cells+1)
    return target,expected,steps


def padded_wrapper(transitions,start,halt):
    """Normalize positive binary input for any fixed binary clockwise R."""
    alphabet=('0','1','L','R','P','F');q0=('initial',);zero=('zeros',)
    seek=('first_one',);trap=('reject_loop',);end=('accepted',)
    states={start,halt}
    for (q,b),(write,target) in transitions.items():
        assert q!=halt and b in '01' and len(write) in (1,2) and set(write)<=set('01')
        states.update((q,target))
    assert start!=halt and all((q,b) in transitions for q in states-{halt} for b in '01')
    rules={}
    def original(q,b):
        write,target=transitions[q,b]
        return tuple(write),end if target==halt else ('run',target)
    for q in (q0,zero,seek,trap):
        for a in alphabet:rules[q,a]=((a,),trap)
    rules[q0,'L']=(('L',),zero)
    rules[zero,'0']=(('P',),zero)
    rules[zero,'1']=(('F',),seek)
    for a in alphabet:rules[seek,a]=((a,),seek)
    rules[seek,'F']=original(start,'1')
    for a in alphabet:rules[trap,a]=((a,),trap)
    for q in states-{halt}:
        for a in alphabet:
            rules[('run',q),a]=original(q,a) if a in '01' else ((a,),('run',q) if a in ('L','R','P') else trap)
    return dict(alphabet=alphabet,transitions=rules,start=q0,halt=end,trap=trap)


def wrapper_trace(original,start,halt,bits,limit=30):
    """Compare entire normalized traces, including every binary microstep."""
    assert bits and set(bits)<=set('01') and '1' in bits
    wrapper=padded_wrapper(original,start,halt)
    binary=binary_compile(wrapper['alphabet'],wrapper['transitions'],wrapper['start'],wrapper['halt'])
    assert binary['a']==4
    original_word=tuple(bits.lstrip('0'));original_state=start
    logical_word=('L',)+tuple(bits)+('R',);logical_state=wrapper['start']
    macros=bitsteps=source_steps=0
    # The first source transition is executed only at the unique F marker.
    while source_steps<limit:
        symbol=logical_word[0]
        source_action=(logical_state==('first_one',) and symbol=='F') or (logical_state[0]=='run' and symbol in '01')
        if source_action:
            if logical_state[0]=='run':assert logical_state[1]==original_state
            active=tuple('1' if a=='F' else a for a in logical_word if a in ('0','1','F'))
            assert active==original_word
            write,next_state=original[original_state,original_word[0]]
            original_word=original_word[1:]+tuple(write);original_state=next_state;source_steps+=1
        logical_state,logical_word,steps=macro(binary,logical_state,logical_word)
        macros+=1;bitsteps+=steps
        if logical_state==wrapper['halt']:
            assert original_state==halt and source_action;break
        assert original_state!=halt
        if source_action:
            # Ignored frame/padding cells may precede the next source cell.
            active=tuple(a for a in logical_word if a in ('0','1'))
            assert active==original_word
        assert macros<(limit+1)*(len(bits)+7)*3
    return dict(input=bits,source_steps=source_steps,logical_steps=macros,
                binary_steps=bitsteps,accepted=logical_state==wrapper['halt'],
                initial_binary_cells=4*len(bits)+8)


def counter_frame(a,z,G0,G1,bits,left,right,state_word='',prefix='',tail=''):
    """Literal word identity only: no free exponent/counter certificate."""
    n=len(bits);assert n>=2 and n&(n-1)==0 and a>=2 and a&(a-1)==0
    assert len(left)==len(right)==a and len(G0)==len(G1) and G0>G1
    K=len(G0);D=2*z*a*K;mu='1'+'0'*(z-1)
    tape_code=lambda bit:'0'*(1+int(bit))+'1'+'0'*(2*z-2-int(bit))
    transport=lambda w:''.join(G1 if b=='1' else G0 for b in w)
    physical=lambda w:''.join(tape_code(b) for b in w)
    c0='0'*a;c1='0'*(a-1)+'1'
    data0,data1=transport(physical(c0)),transport(physical(c1))
    assert len(data0)==len(data1)==D and int(data0,2)<int(data1,2)
    n_cells=a*(n+2);counter=1<<(n_cells-1).bit_length()
    assert counter==2*a*n
    counter_block=transport(mu)
    assert len(counter_block)*counter==D*n
    Q=1<<(D*n);Rdata=(Q-1)//((1<<D)-1)
    Rmu=(Q-1)//((1<<(K*z))-1)
    assert Rmu==(((1<<D)-1)//((1<<(K*z))-1))*Rdata
    data=''.join(data1 if b=='1' else data0 for b in bits)
    pre=prefix+transport(state_word+physical(left));mid=transport(physical(right))
    allword=pre+data+mid+counter_block*counter+tail
    x=int(bits,2);spread=sum(((x>>j)&1)<<(D*j) for j in range(n))
    data_value=int(data0,2)*Rdata+(int(data1,2)-int(data0,2))*spread
    got=((int('1'+pre,2)*Q+data_value)*(1<<len(mid))+int(mid,2))*Q+int(counter_block,2)*Rmu
    got=got*(1<<len(tail))+(int(tail,2) if tail else 0)
    assert got==int('1'+allword,2)
    return dict(a=a,z=z,input_bits=n,tape_cells=n_cells,counter=counter,
                tag_bit_block_length=K,input_block_length=D,counter_block_length=K*z,
                shared_scale_exponent=D*n,word_sha256=hashlib.sha256(allword.encode()).hexdigest())


def fixed_tag_order_checks():
    """Check the actual fixed-halt tracks' first unequal encoded bits.

    Full giant bit blocks need not be materialized: their lengths are exact
    letter counts, and the first difference occurs in their first ten letters.
    """
    import binary_tag_fixed_halt_bridge as bridge
    rows=[]
    for p in range(2,10):
        for variant in range(2):
            alphas=tuple(('01'*(i+variant))[:i%4] for i in range(p))
            packet=bridge.build_tracks(alphas,p-1);u=bridge.materialize(packet)
            assert u[:3]=='bcb'
            phi=bridge.objects(u);beta=packet['beta'];k=packet['padding_u_copies']
            blocks={b:phi[b]+u*k for b in '01'}
            assert blocks['0'].startswith('b'*7+'cb')
            assert blocks['1'].startswith('b'*9+'c')
            e=lambda w:''.join('1'+'0'*beta+'1' if b=='b' else '1' for b in w)
            short=[e(blocks[b][:11]) for b in '01']
            common=7*(beta+2)+1
            assert short[0][:common]==short[1][:common]
            assert short[0][common]=='1' and short[1][common]=='0'
            size=lambda w:w.count('b')*(beta+2)+w.count('c')
            assert size(blocks['0'])==size(blocks['1'])
            rows.append(dict(appendants=p,variant=variant,beta=beta,
                             binary_bit_block_length=size(blocks['0']),
                             first_unequal_bit=common,G0_greater_than_G1=True))
    return rows


def verify():
    rng=random.Random(4082026);local=steps=0;tables=[]
    for alphabet_size in range(2,10):
        alphabet=tuple(str(j) for j in range(alphabet_size));states=('s','p','q','halt')
        transitions={(q,c):(tuple(rng.choice(alphabet) for _ in range(rng.randrange(1,3))),rng.choice(states))
                     for q in states[:-1] for c in alphabet}
        m=binary_compile(alphabet,transitions,'s','halt')
        for _ in range(64):
            q=rng.choice(states[:-1]);word=tuple(rng.choice(alphabet) for _ in range(rng.randrange(1,10)))
            _,_,cost=macro(m,q,word);local+=1;steps+=cost
        tables.append(dict(alphabet=alphabet_size,a=m['a'],states=len({q for q,_ in m['transitions']})+1,
                           binary_instructions=len(m['transitions'])))
    # Actual fixed binary machines, not a generic semantic reference alone.
    machines=[{('s','0'):('1','s'),('s','1'):('0','halt')},
              {('s','0'):('01','p'),('s','1'):('10','p'),('p','0'):('1','s'),('p','1'):('0','halt')},
              {('s','0'):('01','s'),('s','1'):('10','s')}]
    traces=[]
    for t in machines:
        for x in range(1,9):
            for padding in (0,1,4):
                traces.append(wrapper_trace(t,'s','halt','0'*padding+bin(x)[2:],limit=12))
    # Positive-input restriction matters: all-zero inputs enter a defined loop.
    wrapper=padded_wrapper(machines[0],'s','halt')
    for n in range(1,9):
        q=wrapper['start'];w=('L',)+('0',)*n+('R',)
        for _ in range(n+2):write,q=wrapper['transitions'][q,w[0]];w=w[1:]+write
        assert q==wrapper['trap']
    frames=[]
    for _ in range(96):
        a=rng.choice((2,4,8));z=rng.randrange(2,8);K=rng.randrange(2,7)
        x0,x1=sorted(rng.sample(range(1<<K),2),reverse=True)
        G0,G1=format(x0,f'0{K}b'),format(x1,f'0{K}b');n=rng.choice((2,4,8,16))
        x=rng.randrange(1,1<<n);bits=format(x,f'0{n}b')
        left=''.join(rng.choice('01') for _ in range(a));right=''.join(rng.choice('01') for _ in range(a))
        frames.append(counter_frame(a,z,G0,G1,bits,left,right,'0010','10','100'))
    orders=fixed_tag_order_checks()
    return dict(status='PASS_CLOCKWISE_DYADIC_INPUT_NORMALIZATION',
                block_macro_checks=local,binary_steps_in_local_checks=steps,table_ledgers=tables,
                complete_trace_checks=len(traces),traces=traces,all_zero_loops=8,
                counter_frame_checks=len(frames),counter_examples=frames[:8],
                fixed_halt_block_order_checks=len(orders),fixed_halt_block_order_examples=orders,
                scope='Explicit finite binary clockwise transition compiler and padding-normalizing wrapper; exact shared counter scale on dyadic input lengths. Neither dyadic-length enforcement nor a complete Diophantine compiler is supplied.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])

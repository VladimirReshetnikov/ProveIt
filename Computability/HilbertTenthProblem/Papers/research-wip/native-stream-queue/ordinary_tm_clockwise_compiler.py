"""Literal ordinary-TM -> clockwise -> binary-clockwise transition compiler.

No tag production is materialized. Table/state/alphabet counts are effective;
the small fixtures below are not universal machines or arithmetic bounds.
"""
import argparse
from collections import deque
import hashlib
import json
from pathlib import Path
import random

import clockwise_dyadic_input_normalization as binary

LEFT=('left',);RIGHT=('right',);MARK=('marker',)
ENTRY=('entry',);HALT=('halt',);TRAP=('invalid_loop',);SINK=('rejecting_source',)


def positive_input_prelude(states,alphabet,transitions,start,accept,blank='_',reject=()):
    """Erase leading zero padding to blank, then enter the old start on 1."""
    states=tuple(states);alphabet=tuple(alphabet)
    def fresh(name):
        while name in states:name+='_'  # Reserved names stay disjoint from supplied states.
        return name
    prelude=fresh('__positive_input');bad=fresh('__malformed_input')
    delta=dict(transitions)
    for c in alphabet:delta[prelude,c]=(c,'S',bad)
    delta[prelude,'0']=(blank,'R',prelude)
    delta[prelude,'1']=('1','S',start)
    return dict(states=states+(prelude,bad),alphabet=alphabet,transitions=delta,
                start=prelude,accept=accept,blank=blank,reject=tuple(reject)+(bad,))


def compile_positive_tm(states,alphabet,transitions,start,accept,blank='_',reject=()):
    result=compile_tm(**positive_input_prelude(states,alphabet,transitions,start,accept,blank,reject))
    result['positive_input_normalized']=True
    result['original_source_state_count']=len(states)
    return result


def compile_tm(states,alphabet,transitions,start,accept,blank='_',reject=()):
    """TM rules: (state,read)->(write, direction L/R/S, next_state).

    Initial TM head is on the first symbol of the nonempty input word.
    Missing instructions and declared rejecting states become a total loop.
    Supplied state/symbol names are strings; generated names are tagged tuples.
    """
    states=tuple(states);alphabet=tuple(alphabet);reject=set(reject)
    assert len(set(states))==len(states) and all(isinstance(q,str) for q in states)
    assert len(set(alphabet))==len(alphabet) and all(isinstance(c,str) for c in alphabet)
    assert start in states and accept in states and start!=accept
    assert reject<=set(states)-{accept} and {'0','1',blank}<=set(alphabet)
    assert blank not in ('0','1')
    for (q,c),(d,move,p) in transitions.items():
        assert q in states and c in alphabet and d in alphabet and p in states
        assert q!=accept and move in ('L','R','S')
    active=tuple(q for q in states if q not in reject)+(SINK,)
    entry_source=SINK if start in reject else start
    total={}
    for q in active:
        if q==accept:continue
        for c in alphabet:
            d,move,p=transitions.get((q,c),(c,'R',SINK)) if q!=SINK else (c,'R',SINK)
            if p in reject:p=SINK
            total[q,c]=(d,move,p)
    data=lambda c:('data',c)
    # The first four entries preserve the exact ordinary-input/frame code map.
    cw_alphabet=(data('0'),data('1'),LEFT,RIGHT)+tuple(data(c) for c in alphabet if c not in ('0','1'))+(MARK,)
    ordinary_symbols=set(cw_alphabet)-{MARK}

    def dispatch(q,symbol):
        assert symbol in ordinary_symbols
        if q==accept:return (symbol,),HALT
        read=blank if symbol in (LEFT,RIGHT) else symbol[1]
        write,move,target=total[q,read];d=data(write)
        if move=='R':
            if symbol==LEFT:return (LEFT,d),('run',target)
            if symbol==RIGHT:return (d,RIGHT),('right',target)
            return (d,),('run',target)
        if move=='L':
            if symbol==LEFT:return (LEFT,MARK),('carry',target,d)
            if symbol==RIGHT:return (MARK,d),('carry',target,RIGHT)
            return (MARK,),('carry',target,d)
        if symbol==LEFT:return (LEFT,MARK),('stay',target,d)
        if symbol==RIGHT:return (MARK,RIGHT),('stay',target,d)
        return (MARK,),('stay',target,d)

    roots=[ENTRY,TRAP]+[('run',q) for q in active]
    queue=deque(roots);seen=set();rules={}
    while queue:
        state=queue.popleft()
        if state==HALT or state in seen:continue
        seen.add(state)
        for symbol in cw_alphabet:
            if state==ENTRY:
                write,target=((LEFT,),('run',entry_source)) if symbol==LEFT else ((symbol,),TRAP)
            elif state==TRAP:write,target=(symbol,),TRAP
            elif state[0]=='run':
                write,target=dispatch(state[1],symbol) if symbol!=MARK else ((symbol,),TRAP)
            elif state[0]=='right':
                if symbol==RIGHT:write,target=dispatch(state[1],RIGHT)
                elif symbol==MARK:write,target=(symbol,),TRAP
                else:write,target=(symbol,),state
            elif state[0]=='carry':
                if symbol==MARK:write,target=dispatch(state[1],state[2])
                else:write,target=(state[2],),('carry',state[1],symbol)
            else:
                assert state[0]=='stay'
                write,target=dispatch(state[1],state[2]) if symbol==MARK else ((symbol,),state)
            assert len(write) in (1,2) and all(c in cw_alphabet for c in write)
            rules[state,symbol]=(write,target)
            if target!=HALT and target not in seen:queue.append(target)
    assert all((q,c) in rules for q in seen for c in cw_alphabet)
    return dict(states=states,source_alphabet=alphabet,source_start=entry_source,
                source_accept=accept,blank=blank,source_total=total,
                alphabet=cw_alphabet,transitions=rules,start=ENTRY,halt=HALT,
                clockwise_states=tuple(sorted(seen|{HALT},key=repr)))


def initial(machine,bits):
    assert bits and set(bits)<=set('01')
    return ENTRY,(LEFT,)+tuple(('data',b) for b in bits)+(RIGHT,)


def step(machine,state,word):
    write,target=machine['transitions'][state,word[0]]
    return target,word[1:]+tuple(write)


def checkpoint(state,word):
    if state[0]=='run':return state[1],word[0]
    if state[0]=='right' and word[0]==RIGHT:return state[1],RIGHT
    if state[0] in ('carry','stay') and word[0]==MARK:return state[1],state[2]
    return None


def decode_checkpoint(machine,state,word):
    q,held=checkpoint(state,word)
    data=((held,)+word[1:]) if word[0]==MARK else word
    assert data.count(LEFT)==data.count(RIGHT)==1 and MARK not in data
    i=data.index(LEFT);ordered=data[i:]+data[:i]
    assert ordered[-1]==RIGHT and all(c[0]=='data' for c in ordered[1:-1])
    # Head coordinate relative to the first represented ordinary tape cell.
    index=(-i)%len(data)
    return q,tuple(c[1] for c in ordered[1:-1]),index-1


def ordinary_macro(machine,state,word,binary_machine=None):
    """Execute one ordinary instruction up to the next encoded checkpoint."""
    assert checkpoint(state,word) and checkpoint(state,word)[0]!=machine['source_accept']
    oldsize=len(word);count=bitsteps=0
    while True:
        before_state,before_word=state,word
        state,word=step(machine,state,word);count+=1
        if binary_machine is not None:
            gotstate,gotword,used=binary.macro(binary_machine,before_state,before_word)
            assert (gotstate,gotword)==(state,word);bitsteps+=used
        assert state!=HALT and count<=oldsize+1
        if checkpoint(state,word):return state,word,count,bitsteps


def binary_compile(machine):
    return binary.binary_compile(machine['alphabet'],machine['transitions'],ENTRY,HALT)


def ledger(machine,bm=None):
    bm=binary_compile(machine) if bm is None else bm
    Q=len({q for q,_ in bm['transitions']})+1
    a=bm['a'];z=30*Q+61;p=2*z;beta=10*p
    C=len(machine['clockwise_states'])
    E=len(set(machine['transitions'].values()))
    assert Q==(C-1)*(1<<(a-1))+(2*a-1)*E+2
    assert a&(a-1)==0 and bm['codes'][('data','0')]=='0'*a
    assert bm['codes'][('data','1')]=='0'*(a-1)+'1'
    return dict(source_states=len(machine['states']),source_symbols=len(machine['source_alphabet']),
                original_source_states=machine.get('original_source_state_count',len(machine['states'])),
                positive_input_normalized=machine.get('positive_input_normalized',False),
                clockwise_states=C,clockwise_symbols=len(machine['alphabet']),
                clockwise_instructions=len(machine['transitions']),binary_block_width=a,
                distinct_clockwise_output_target_pairs=E,
                binary_states=Q,binary_instructions=len(bm['transitions']),
                initial_length_a=a,initial_length_b=2*a,cts_z=z,cts_appendants=p,tag_deletion=beta,
                tag_production_materialized=False)


def trace(machine,bits,limit=24,bm=None):
    """Compare every encoded checkpoint to an ordinary sparse-tape machine."""
    state,word=initial(machine,bits);bitsteps=0
    if bm is not None:
        target,output,used=binary.macro(bm,state,word);bitsteps+=used
        assert (target,output)==step(machine,state,word)
    state,word=step(machine,state,word)
    tape={i:c for i,c in enumerate(bits)};head=0;lo=0;hi=len(bits)-1
    q=machine['source_start'];cwsteps=1;ordinary=0;left=right=stays=blank_writes=0
    while True:
        gotq,gotdata,relative=decode_checkpoint(machine,state,word)
        assert gotq==q and gotdata==tuple(tape.get(i,machine['blank']) for i in range(lo,hi+1))
        assert lo+relative==head and lo-1<=head<=hi+1
        if q==machine['source_accept']:
            if bm is not None:
                target,output,used=binary.macro(bm,state,word);bitsteps+=used
                assert (target,output)==step(machine,state,word)
            state,word=step(machine,state,word);cwsteps+=1
            assert state==HALT
            break
        if ordinary==limit:break
        read=tape.get(head,machine['blank']);write,move,target=machine['source_total'][q,read]
        left+=head<lo;right+=head>hi;stays+=move=='S';blank_writes+=write==machine['blank']
        lo=min(lo,head);hi=max(hi,head);tape[head]=write
        head+=-1 if move=='L' else 1 if move=='R' else 0;q=target;ordinary+=1
        state,word,used,bused=ordinary_macro(machine,state,word,bm);cwsteps+=used;bitsteps+=bused
    return dict(input=bits,ordinary_steps=ordinary,clockwise_steps=cwsteps,
                checked_binary_microsteps=bitsteps,accepted=state==HALT,
                left_extensions=left,right_extensions=right,stay_steps=stays,blank_writes=blank_writes)


def serialize_table(machine):
    return [[q,c,list(write),target] for (q,c),(write,target) in
            sorted(machine['transitions'].items(),key=lambda item:repr(item[0]))]


def verify():
    rng=random.Random(20261002);traces=[];ledgers=[];compiled=[]
    # Explicit deterministic cases force both boundary extensions, blank writes,
    # stay moves, accepting dispatch from every phase, and rejecting gaps.
    fixtures=[
        (('s','l','r','h'),{('s','0'):('_','L','l'),('s','1'):('_','L','l'),
          ('l','_'):('1','L','r'),('r','_'):('_','R','h')}),
        (('s','r','h'),{('s','0'):('_','R','r'),('s','1'):('_','R','r'),
          ('r','_'):('1','R','h'),('r','0'):('0','R','r'),('r','1'):('1','R','r')}),
        (('s','p','h'),{('s','0'):('1','S','p'),('s','1'):('_','S','p'),
          ('p','_'):('_','S','h'),('p','1'):('0','L','h')}),
        (('s','r','h'),{('s','1'):('0','L','r')}),
    ]
    for states,delta in fixtures:
        machine=compile_tm(states,('0','1','_'),delta,'s','h')
        bm=binary_compile(machine);compiled.append((machine,bm));ledgers.append(ledger(machine,bm))
        for x in range(1,9):
            for pad in (0,2):traces.append(trace(machine,'0'*pad+bin(x)[2:],20,bm))
    for case in range(32):
        states=('s','p','q','reject','h');alphabet=('0','1','_','x')
        delta={(q,c):(rng.choice(alphabet),rng.choice('LRS'),rng.choice(states))
               for q in states[:-2] for c in alphabet if rng.randrange(5)}
        machine=compile_tm(states,alphabet,delta,'s','h',reject=('reject',))
        for _ in range(12):
            n=rng.randrange(1,10);bits=''.join(rng.choice('01') for _ in range(n))
            traces.append(trace(machine,bits,32))
        if case<4:ledgers.append(ledger(machine))
    prelude_checks=0
    for states,delta in fixtures:
        wrapped=compile_positive_tm(states,('0','1','_'),delta,'s','h')
        bm=binary_compile(wrapped);ledgers.append(ledger(wrapped,bm))
        for x in range(1,9):
            for padding in (0,1,4):
                bits='0'*padding+bin(x)[2:]
                state,word=initial(wrapped,bits);state,word=step(wrapped,state,word)
                for _ in range(padding+1):state,word,_,_=ordinary_macro(wrapped,state,word)
                q,data,relative=decode_checkpoint(wrapped,state,word)
                assert q=='s' and relative==padding
                assert data==('_',)*padding+tuple(bin(x)[2:]);prelude_checks+=1
                traces.append(trace(wrapped,bits,20,bm))
    zero_checks=0
    for n in range(1,9):
        outcome=trace(wrapped,'0'*n,n+5,bm)
        assert not outcome['accepted'];zero_checks+=1
    # Full table serialization is finite and independently reconstructible.
    sample=compiled[0][0];table=serialize_table(sample)
    wire=json.dumps(table,separators=(',',':'))
    assert len(table)==len(sample['transitions'])
    return dict(status='PASS_ORDINARY_TM_CLOCKWISE_COMPILER',full_trace_checks=len(traces),
                ordinary_steps=sum(t['ordinary_steps'] for t in traces),
                clockwise_steps=sum(t['clockwise_steps'] for t in traces),
                binary_microsteps=sum(t['checked_binary_microsteps'] for t in traces),
                left_extensions=sum(t['left_extensions'] for t in traces),
                right_extensions=sum(t['right_extensions'] for t in traces),
                blank_writes=sum(t['blank_writes'] for t in traces),
                stay_steps=sum(t['stay_steps'] for t in traces),
                accepting_traces=sum(t['accepted'] for t in traces),
                positive_prelude_checkpoint_checks=prelude_checks,
                all_zero_nonhalting_checks=zero_checks,
                table_ledgers=ledgers,illustrative_transition_table=table,
                illustrative_table_sha256=hashlib.sha256(wire.encode()).hexdigest(),
                trace_examples=traces[:16],
                scope='Effective finite tables and exact input convention for each supplied ordinary TM; no universal table is instantiated, no tag production is materialized, and no arithmetic operation bound is asserted.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])

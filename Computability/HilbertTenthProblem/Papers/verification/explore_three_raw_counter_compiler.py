#!/usr/bin/env python3
"""Finite compiler for ordinary input, three logical counters and serial signs."""
from pathlib import Path
from itertools import product
import json


class Builder:
    def __init__(self):self.code={};self.serial=0
    def fresh(self,prefix='L'):
        self.serial+=1;return f'{prefix}_{self.serial}'
    def emit(self,label,*instruction):
        assert label not in self.code
        self.code[label]=tuple(instruction);return label
    def incs(self,register,count,target):
        for _ in range(count):
            label=self.fresh('inc');self.emit(label,'inc',register,target);target=label
        return target
    def transfer(self,source,target,continuation):
        loop=self.fresh('transfer')
        self.emit(loop,'dec',source,continuation,self.incs(target,1,loop))
        return loop
    def push(self,register,base,digit,continuation):
        assert register in (0,1) and 1<=digit<base
        after=self.incs(register,digit,continuation)
        restore=self.transfer(2,register,after)
        loop=self.fresh('push')
        self.emit(loop,'dec',register,restore,self.incs(2,base,loop))
        return loop
    def pop(self,register,base,continuations):
        assert register in (0,1) and len(continuations)==base
        loops=[self.fresh('pop') for _ in range(base)]
        for j in range(base):
            restore=self.transfer(2,register,continuations[j])
            next_loop=loops[(j+1)%base]
            if j==base-1:next_loop=self.incs(2,1,next_loop)
            self.emit(loops[j],'dec',register,restore,next_loop)
        return loops[0]


def step(code,pc,values):
    instruction=code[pc];kind=instruction[0];after=list(values)
    if kind=='inc':
        _,register,target=instruction;after[register]+=1;branch='inc'
    elif kind=='dec':
        _,register,zero,nonzero=instruction
        if after[register]==0:target=zero;branch='zero'
        else:after[register]-=1;target=nonzero;branch='nonzero'
    elif kind=='jump':_,target=instruction;branch='jump'
    else:raise AssertionError(instruction)
    return target,after,branch


def run(code,start,values,stop=None,callback=None,limit=2000000):
    pc=start;values=list(values);steps=0
    while code[pc][0]!='halt' and pc!=stop:
        assert steps<limit,(pc,values,'finite execution limit exceeded')
        target,after,branch=step(code,pc,values)
        if callback is not None:callback(pc,values,branch,target,after)
        pc,values=target,after;steps+=1
    return pc,values,steps


def stack_word(symbols,codes,base):
    return sum(codes[s]*base**i for i,s in enumerate(symbols))


def compile_tm(alphabet,blank,transitions,start,accept,reject):
    assert blank in alphabet and '0' in alphabet and '1' in alphabet
    assert set(accept).isdisjoint(reject)
    codes={symbol:i+1 for i,symbol in enumerate(alphabet)};symbols={v:k for k,v in codes.items()}
    base=len(alphabet)+1;b=Builder()
    b.emit('accept','halt',True);b.emit('reject','halt',False)
    cleanup='accept'
    for register in reversed(range(3)):
        loop=b.fresh('cleanup');b.emit(loop,'dec',register,cleanup,loop);cleanup=loop
    states={start}|set(accept)|set(reject)|{q for q,_ in transitions}|{v[0] for v in transitions.values()}
    def entry(state):return f'tm:{state}'
    for state in sorted(states):
        if state in accept:b.emit(entry(state),'jump',cleanup);continue
        if state in reject:b.emit(entry(state),'jump','reject');continue
        callbacks=[]
        for remainder in range(base):
            scanned=blank if remainder==0 else symbols[remainder]
            transition=transitions.get((state,scanned))
            if transition is None:callbacks.append('reject');continue
            target,written,direction=transition
            assert written in codes and direction in ('L','R','S')
            continuation=entry(target)
            if direction=='R':target_entry=b.push(0,base,codes[written],continuation)
            elif direction=='S':target_entry=b.push(1,base,codes[written],continuation)
            else:
                left_callbacks=[]
                for left in range(base):
                    new_head=blank if left==0 else symbols[left]
                    second=b.push(1,base,codes[new_head],continuation)
                    left_callbacks.append(b.push(1,base,codes[written],second))
                target_entry=b.pop(0,base,left_callbacks)
            callbacks.append(target_entry)
        b.emit(entry(state),'jump',b.pop(1,base,callbacks))
    loader=b.fresh('loader')
    load_callbacks=[b.push(1,base,codes[str(bit)],loader) for bit in (0,1)]
    load_pop=b.pop(0,2,load_callbacks)
    b.emit(loader,'dec',0,entry(start),b.incs(0,1,load_pop))
    assert all(target in b.code for ins in b.code.values() for target in
               ([ins[2]] if ins[0]=='inc' else list(ins[2:]) if ins[0]=='dec' else [ins[1]] if ins[0]=='jump' else []))
    return dict(code=b.code,start=loader,tm_start=entry(start),codes=codes,base=base,
                alphabet=alphabet,blank=blank,transitions=transitions,initial_state=start,
                accept=set(accept),reject=set(reject))


def physical_phases(instruction,branch):
    kind=instruction[0];plus=(1,1,1);minus=(-1,-1,-1);zeros=(0,0,0)
    if kind=='inc':
        register=instruction[1];second=tuple(1 if i==register else -1 for i in range(3))
        assert branch=='inc';return [(plus,zeros),(second,zeros)]
    if kind=='dec':
        register=instruction[1]
        if branch=='zero':return [(plus,tuple(int(i==register) for i in range(3))),(minus,zeros)]
        assert branch=='nonzero'
        return [(tuple(-1 if i==register else 1 for i in range(3)),zeros),(minus,zeros)]
    assert kind=='jump' and branch=='jump';return [(plus,zeros),(minus,zeros)]


def serial_graph(code,start):
    nodes={};edges=set();entries={};macros={}
    for pc,instruction in code.items():
        if instruction[0]=='halt':
            name=(pc,'halt',0,0);nodes[name]=(0,1,0);entries[pc]=[name];continue
        branches=['zero','nonzero'] if instruction[0]=='dec' else [instruction[0]]
        entries[pc]=[]
        for branch in branches:
            phases=physical_phases(instruction,branch);sequence=[]
            for phase,(signs,zeros) in enumerate(phases):
                for lane in range(3):
                    name=(pc,branch,phase,lane);nodes[name]=(lane,signs[lane],zeros[lane]);sequence.append(name)
            edges.update(zip(sequence,sequence[1:]));entries[pc].append(sequence[0]);macros[(pc,branch)]=sequence
    for (pc,branch),sequence in macros.items():
        instruction=code[pc]
        target=instruction[2] if instruction[0]=='inc' else instruction[1] if instruction[0]=='jump' else instruction[2 if branch=='zero' else 3]
        edges.update((sequence[-1],next_entry) for next_entry in entries[target])
    prefix=[]
    for phase,sign in enumerate((1,-1)):
        for lane in range(3):
            name=('prefix','jump',phase,lane);nodes[name]=(lane,sign,0);prefix.append(name)
    edges.update(zip(prefix,prefix[1:]));edges.update((prefix[-1],entry) for entry in entries[start])
    assert all(u!=v and nodes[v][0]==(nodes[u][0]+1)%3 for u,v in edges)
    assert nodes[prefix[0]]==(0,1,0)
    return dict(nodes=nodes,edges=edges,entries=entries,macros=macros,prefix=prefix,
                initial=prefix[0],final=entries['accept'][0])


def apply_serial(nodes,sequence,physical):
    physical=list(physical)
    for node in sequence:
        lane,sign,zero=nodes[node]
        if zero and physical[lane]!=0:return None
        physical[lane]+=sign
        if physical[lane]<0:return None
    return physical


def verify_macros():
    cases=bad=0
    for register in range(3):
        for logical in product(range(5),repeat=3):
            for instruction,branch in [(('inc',register,'end'),'inc'),
                                       (('dec',register,'end','end'),'zero'),
                                       (('dec',register,'end','end'),'nonzero')]:
                phases=physical_phases(instruction,branch);nodes={};sequence=[]
                for phase,(signs,zeros) in enumerate(phases):
                    for lane in range(3):
                        node=(phase,lane);nodes[node]=(lane,signs[lane],zeros[lane]);sequence.append(node)
                actual=apply_serial(nodes,sequence,[2*n for n in logical])
                valid=branch=='inc' or (logical[register]==0 if branch=='zero' else logical[register]>0)
                assert (actual is not None)==valid
                if valid:
                    expected=list(logical)
                    if branch=='inc':expected[register]+=1
                    if branch=='nonzero':expected[register]-=1
                    assert actual==[2*n for n in expected]
                else:bad+=1
                cases+=1
    return dict(local_instruction_cases=cases,wrong_branches_rejected=bad)


def verify_stack_routines():
    cases=steps=0
    for base in range(2,7):
        for register in (0,1):
            for value in range(41):
                for digit in range(1,base):
                    b=Builder();b.emit('end','halt',True);entry=b.push(register,base,digit,'end')
                    initial=[7,7,0];initial[register]=value
                    _,actual,n=run(b.code,entry,initial)
                    expected=initial[:];expected[register]=base*value+digit
                    assert actual==expected;cases+=1;steps+=n
                b=Builder();callbacks=[]
                for remainder in range(base):callbacks.append(b.emit(f'remainder:{remainder}','halt',True))
                entry=b.pop(register,base,callbacks);initial=[7,7,0];initial[register]=value
                pc,actual,n=run(b.code,entry,initial)
                expected=initial[:];expected[register]=value//base
                assert actual==expected and pc==callbacks[value%base];cases+=1;steps+=n
    return dict(complete_routine_cases=cases,counter_instructions=steps)


def sample_machine():
    alphabet=['_','0','1'];transitions={}
    for first in ('0','1'):
        transitions[('start',first)]=(f'seek{first}',first,'R')
        for digit in ('0','1'):transitions[(f'seek{first}',digit)]=(f'seek{first}',digit,'R')
        transitions[(f'seek{first}','_')]=(f'check{first}','_','L')
        for last in ('0','1'):
            transitions[(f'check{first}',last)]=('accept' if first==last else 'reject',last,'S')
    return compile_tm(alphabet,'_',transitions,'start',{'accept'},{'reject'})


def direct_tm(machine,x):
    tape={i:s for i,s in enumerate(bin(x)[2:])};head=0;state=machine['initial_state'];steps=0
    while state not in machine['accept']|machine['reject']:
        transition=machine['transitions'].get((state,tape.get(head,machine['blank'])))
        if transition is None:return False,steps
        state,written,direction=transition;tape[head]=written
        head+=1 if direction=='R' else -1 if direction=='L' else 0;steps+=1
        assert steps<1000
    return state in machine['accept'],steps


def verify_full_compiler():
    machine=sample_machine();code=machine['code'];graph=serial_graph(code,machine['start'])
    loader_steps=logical_steps=physical_blocks=accepted=rejected=0;traces=[]
    for x in range(1,32):
        _,loaded,n=run(code,machine['start'],[x,0,0],stop=machine['tm_start'])
        assert loaded==[0,stack_word(bin(x)[2:],machine['codes'],machine['base']),0]
        loader_steps+=n
        expected,tm_steps=direct_tm(machine,x)
        if x<=7:
            physical=[2*x,0,0];physical=apply_serial(graph['nodes'],graph['prefix'],physical)
            assert physical==[2*x,0,0];previous=graph['prefix'][-1];blocks=6
            def check_step(pc,before,branch,target,after):
                nonlocal physical,previous,blocks
                sequence=graph['macros'][(pc,branch)]
                assert (previous,sequence[0]) in graph['edges']
                assert physical==[2*n for n in before]
                physical=apply_serial(graph['nodes'],sequence,physical)
                assert physical==[2*n for n in after]
                previous=sequence[-1];blocks+=6
            halt,values,n=run(code,machine['start'],[x,0,0],callback=check_step)
            assert (previous,graph['entries'][halt][0]) in graph['edges']
            assert (graph['entries'][halt][0]==graph['final'])==expected
            if expected:assert physical==[0,0,0] and blocks%6==0
            physical_blocks+=blocks
            traces.append(dict(x=x,accepted=expected,logical_instructions=n,serial_blocks=blocks,
                               final_logical=values,tm_steps=tm_steps))
        else:halt,values,n=run(code,machine['start'],[x,0,0])
        assert code[halt]==('halt',expected) and expected==(x%2==1)
        if expected:assert values==[0,0,0];accepted+=1
        else:rejected+=1
        logical_steps+=n
    return dict(fixed_counter_locations=len(code),fixed_serial_vertices=len(graph['nodes']),
                fixed_serial_edges=len(graph['edges']),raw_inputs=31,accepted=accepted,rejected=rejected,
                loader_instructions=loader_steps,total_counter_instructions=logical_steps,
                checked_serial_blocks=physical_blocks,complete_serial_traces=traces,
                scope='One fixed compiled Turing machine on raw1..31, including right/left/stay moves and both halts; raw1..7 also follow every labelled serial edge and source zero test. General universality is the written constructive theorem.')


def verify():
    return dict(status='PASS_THREE_RAW_COUNTER_UNIVERSAL_COMPILER',
                stack_routines=verify_stack_routines(),signed_macros=verify_macros(),
                complete_compiler=verify_full_compiler(),
                proof='../1980/EXPLORATION_THREE_RAW_COUNTER_UNIVERSAL_COMPILER.md',
                universal_interface=dict(operations=123,products=56,additions=67,positive_unknowns=45,equations=33,
                                         dependency='EXPLORATION_SERIAL_RAW_COUNTER_COMPOSITION.md'),
                scope='Constructive strong ordinary-input compiler and finite exact regressions. The123-operation arithmetic is inherited from its independently audited complete composition; the universal frontier remains90.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['stack_routines']);print(result['signed_macros'])
    print({k:v for k,v in result['complete_compiler'].items() if k not in ('scope','complete_serial_traces')})

"""Fixed-space seven-symbol queue, explicit padding normalizer, and radix bound."""
from pathlib import Path
from itertools import product
import json
import sympy as sp
import explore_finite_state_raw_queue as old

State=old.State
PLAIN=old.PLAIN
MARKED=old.MARKED
DELIM=old.DELIM
ALPHABET=old.ALPHABET
BLANK=old.BLANK
C_RADIX=243


class Machine(old.Machine):
    """A one-sided three-symbol TM; transitions can sense the left boundary."""
    def __init__(self,name,transitions,initial='s',accept=('accept',),reject=('reject',)):
        self.name=name;self.delta=dict(transitions);self.initial=initial
        self.accept=set(accept);self.reject=set(reject)
        assert not self.accept & self.reject
        self.states={initial}|self.accept|self.reject|{q for q,_,_ in self.delta}|{v[0] for v in self.delta.values()}
        assert all(a in range(3) and b in range(3) and left in (False,True) and move in (-1,0,1)
                   for (_,a,left),(_,b,move) in self.delta.items())

    def queue_transition(self,state,symbol):
        assert symbol in ALPHABET
        if state.kind!='scan':return super().queue_transition(state,symbol)
        bad=(State('loop'),(DELIM,),'reject')
        if symbol==DELIM:
            if not state.seen or state.previous is None or state.right:return bad
            return self.start(state.next_q),(state.previous,DELIM),'pass'
        a,mark=symbol
        prev=state.previous;seen=state.seen;right=state.right;nq=state.next_q
        if mark==2:
            if seen or right:return bad
            entry=self.delta.get((state.q,a,prev is None))
            if entry is None:return bad
            nq,b,move=entry;seen=True
            if move==-1:
                if prev is None or prev[1]!=0:return bad
                out=(MARKED[prev[0]],);current=PLAIN[b]
            else:
                out=() if prev is None else (prev,)
                current=MARKED[b] if move==0 else PLAIN[b]
                right=move==1
        else:
            out=() if prev is None else (prev,)
            current=MARKED[a] if right else PLAIN[a];right=False
        return State('scan',state.q,current,nq,seen,right),out,''


def left_aware(machine):
    return Machine(machine.name,{(q,a,left):entry for (q,a),entry in machine.delta.items()
                                  for left in (False,True)},machine.initial,machine.accept,machine.reject)


def with_normalizer(client):
    """Erase complete high 00 pairs in place, preserving one pair for input zero."""
    names=['norm.scan','norm.second','norm.first0','norm.first1',
           'norm.erase_second','norm.over_first','norm.return','norm.reject']
    assert not set(names)&client.states
    delta=dict(client.delta)
    bad='norm.reject'
    for left in (False,True):
        for a in range(3):
            delta['norm.scan',a,left]=('norm.scan',a,1) if a!=BLANK else (
                (bad,a,0) if left else ('norm.second',a,-1))
            delta['norm.second',a,left]=((bad,a,0) if left or a==BLANK else (f'norm.first{a}',a,-1))
            for b in (0,1):
                q=f'norm.first{b}'
                if a==BLANK or (a,b)==(1,1):entry=(bad,a,0)
                elif (a,b)==(0,0):
                    entry=(client.initial,a,0) if left else ('norm.erase_second',BLANK,1)
                else:entry=(client.initial,a,0) if left else ('norm.return',a,-1)
                delta[q,a,left]=entry
            delta['norm.erase_second',a,left]=(bad,a,0) if left or a!=0 else ('norm.over_first',BLANK,-1)
            delta['norm.over_first',a,left]=(bad,a,0) if left or a!=BLANK else ('norm.second',a,-1)
            delta['norm.return',a,left]=(client.initial,a,0) if left else ('norm.return',a,-1)
    result=Machine(client.name,delta,'norm.scan',client.accept,client.reject|{bad})
    result.client_initial=client.initial
    result.client_states=set(client.states)
    return result


def canonical_bits(x):
    digits=[]
    while x:
        digits.append(x%3);x//=3
    if not digits:digits=[0]
    return [b for a in digits for b in (a//2,a%2)]


def direct_step(machine,q,tape,head):
    entry=machine.delta.get((q,tape[head],head==0))
    if entry is None:return None,'undefined'
    nq,b,move=entry;nh=head+move
    if nh<0:return None,'left'
    if nh>=len(tape):return None,'right'
    result=list(tape);result[head]=b
    return (nq,result,nh),''


def fixtures():
    clients=[left_aware(m) for m in old.fixtures()]
    delta={}
    for a in range(3):
        delta['s',a,True]=('back',a,1)
        delta['s',a,False]=('reject',a,0)
        delta['back',a,False]=('home',a,-1)
        delta['back',a,True]=('reject',a,0)
        for left in (False,True):delta['home',a,left]=('accept' if left else 'reject',a,0)
    clients.append(Machine('left_sensor',delta))
    return [with_normalizer(c) for c in clients]


def verify_radix_source():
    x,L,alpha,R,N0,N1,Winit=sp.symbols('x L alpha R N0 N1 Winit')
    dag=[('L_square','*','L','L'),('radix','*',C_RADIX,'L_square'),
         ('initial_length','*',3,'L'),('input_bound','+','x','alpha')]
    env=dict(x=x,L=L,alpha=alpha,R=R,N0=N0,N1=N1,Winit=Winit)
    for name,op,a,b in dag:
        a=env[a] if isinstance(a,str) else a;b=env[b] if isinstance(b,str) else b
        env[name]=a*b if op=='*' else a+b
    comparisons=[('R','radix'),('Winit','initial_length'),('input_bound','L'),('N0','x'),('N1','L')]
    residuals=[R-C_RADIX*L**2,Winit-3*L,x+alpha-L,N0-x,N1-L]
    assert all(sp.expand(env[a]-env[b]-r)==0 for (a,b),r in zip(comparisons,residuals))
    powers=[];nonpowers=0
    for value in range(1,244):
        radix=C_RADIX*value*value;v=radix
        while v%3==0:v//=3
        if v==1:powers.append(value)
        else:nonpowers+=1
    assert powers==[1,3,9,27,81,243]
    return dict(operations=4,multiplications=3,additions=1,dag=dag,
                comparisons=comparisons,residuals=[sp.sstr(r) for r in residuals],
                radix_only_operations=2,radix_constant=C_RADIX,
                power_checks=len(powers),nonpower_checks=nonpowers,
                scope='Four-operation initialization/radix interface only. R divides an externally certified power of three; row geometry and the history certificate are not counted.')


def verify_runs():
    counts=dict(machines=0,compiled_states=0,compiled_entries=0,padded_inputs=0,normalizations=0,
                exact_tm_steps=0,normalizer_steps=0,client_steps=0,queue_steps=0,
                accepted=0,rejected=0,named_stay_cutoffs=0,left_overflows=0,right_overflows=0,
                zero_inputs=0,high_zero_paddings=0,phase_length_checks=0,strict_radix_checks=0)
    padding_results={};max_table_append=0
    for machine in fixtures():
        state0,table,states=machine.compile()
        assert len(table)==7*len(states)
        assert max(len(out) for _,out,_ in table.values())<=2
        counts['machines']+=1;counts['compiled_states']+=len(states);counts['compiled_entries']+=len(table)
        max_table_append=max(max_table_append,max(len(out) for _,out,_ in table.values()))
        for x in range(32):
            minimal=1
            while 3**minimal<=x:minimal+=1
            for pad in (0,1,2):
                ell=minimal+pad;L=3**ell;R=C_RADIX*L*L;full=2*ell+2
                word=tuple(PLAIN[(x//3**i)%3] for i in range(ell))+(DELIM,);state=state0
                assert old.coordinate(word,0)==x and old.coordinate(word,1)==L
                assert 3**len(word)==3*L and x<L

                def step():
                    nonlocal state,word
                    W=3**len(word);nxt,out,event=table[state,word[0]]
                    assert len(word)<=full and W<=9*L*L
                    for i in range(2):
                        ni=old.coordinate(word,i);ui=old.coordinate(out,i)
                        assert 0<=ni<W and 0<=ui<=8
                        assert ni+ui*W<81*L*L<R
                        assert 0<=word[0][i]+3*old.coordinate(word[1:]+out,i)<R
                    assert 3**len(out)*W<=81*L*L<R
                    before_kind=state.kind
                    state,word,event=old.one_queue_step(machine,state,word,table)
                    assert len(word)<=full
                    if before_kind=='scan' and event!='reject':
                        assert len(word) in (full-1,full);counts['phase_length_checks']+=1
                    counts['strict_radix_checks']+=1;counts['queue_steps']+=1
                    return event

                for _ in range(ell+1):event=step()
                assert event=='loaded' and len(word)==full
                tape,head=old.decode_tape(word)
                assert tape==[b for i in range(ell) for b in ((x//3**i%3)//2,(x//3**i%3)%2)]+[BLANK]
                assert head==0;q=machine.initial;normalized=False
                for _ in range(200):
                    if q in machine.accept|machine.reject:break
                    direct,reason=direct_step(machine,q,tape,head)
                    while True:
                        event=step()
                        if event in ('pass','reject'):break
                        assert word
                    if direct is None:
                        assert event=='reject' and state.kind=='loop'
                        if reason in ('left','right'):counts[reason+'_overflows']+=1
                        q='norm.reject';break
                    assert event=='pass' and len(word)==full
                    was_normalizer=q.startswith('norm.')
                    q,tape,head=direct
                    assert old.decode_tape(word)==(tape,head)
                    expected='drain' if q in machine.accept else 'loop' if q in machine.reject else 'scan'
                    assert state.kind==expected
                    if state.kind=='scan':assert state.q==q and state.previous is None
                    counts['exact_tm_steps']+=1;counts['normalizer_steps' if was_normalizer else 'client_steps']+=1
                    if was_normalizer and q==machine.client_initial:
                        assert not normalized
                        wanted=canonical_bits(x)
                        assert tape==wanted+[BLANK]*(2*ell+1-len(wanted)) and head==0
                        normalized=True;counts['normalizations']+=1
                assert normalized
                if q in machine.accept:
                    assert state.kind=='drain'
                    while word:step()
                    result='accept';counts['accepted']+=1
                elif q in machine.reject or state.kind=='loop':
                    assert word and state.kind=='loop'
                    length=len(word)
                    for _ in range(5):step()
                    assert len(word)==length;result='reject';counts['rejected']+=1
                else:
                    assert machine.name=='infinite_stay' and word
                    result='cutoff';counts['named_stay_cutoffs']+=1
                padding_results[machine.name,x,pad]=result
                counts['padded_inputs']+=1;counts['zero_inputs']+=x==0;counts['high_zero_paddings']+=pad>0
    for x in range(32):
        assert padding_results['right_growth',x,0]=='reject'
        assert padding_results['right_growth',x,1]==padding_results['right_growth',x,2]=='accept'
        for name in ('initial_accept','initial_reject','undefined','scan_accept','left_growth',
                     'double_left','stay_accept','infinite_right','infinite_stay','binary_parity','left_sensor'):
            assert len({padding_results[name,x,pad] for pad in (0,1,2)})==1
    machine=fixtures()[0];state=State('load_first');word=(DELIM,)
    assert old.coordinate(word,0)==0 and old.coordinate(word,1)==1 and 3**len(word)==3
    state,word,event=old.one_queue_step(machine,state,word)
    assert event=='reject' and state.kind=='loop' and word
    return counts|dict(maximum_table_append=max_table_append,explicit_ell_zero_rejection=1,
                       accepting_only_after_wider_padding=32,
                       scope='Cutoffs occur only for the named stationary nonhalting test. Every completed queue scan is compared with an independent bounded TM step.')


def verify_all_single_scans():
    counts=dict(cases=0,queue_steps=0,left_rejections=0,right_rejections=0,valid_passes=0)
    for length in range(1,5):
        for tape in product(range(3),repeat=length):
            for head in range(length):
                for write,move in product(range(3),(-1,0,1)):
                    machine=Machine('one',{('s',a,left):('accept',write,move) for a in range(3) for left in (False,True)})
                    word=tuple(MARKED[a] if i==head else PLAIN[a] for i,a in enumerate(tape))+(DELIM,)
                    state=machine.start('s');direct,reason=direct_step(machine,'s',list(tape),head)
                    while True:
                        state,word,event=old.one_queue_step(machine,state,word);counts['queue_steps']+=1
                        assert word and len(word)<=length+1
                        if event in ('pass','reject'):break
                    if direct is None:
                        assert reason in ('left','right') and event=='reject' and state.kind=='loop'
                        counts[reason+'_rejections']+=1
                    else:
                        q,expected,nh=direct
                        assert event=='pass' and state.kind=='drain'
                        assert old.decode_tape(word)==(expected,nh) and len(word)==length+1
                        counts['valid_passes']+=1
                    counts['cases']+=1
    return counts


def verify():
    return dict(status='PASS_FIXED_SPACE_RAW_QUEUE',source=verify_radix_source(),
                runs=verify_runs(),all_short_scans=verify_all_single_scans(),
                proof='../1980/EXPLORATION_FIXED_SPACE_RAW_QUEUE.md',
                review_status='Author and independent root/binary_encoding full proof/source audits and fresh verify runs PASS; no mathematical findings. Publication is separate.',
                scope='Fixed-space ordinary-input queue and existential-padding universality. The four-operation raw initialization/radix interface is exact; no total Diophantine verifier count or tag-system composition is claimed.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['runs']);print(result['all_short_scans'])

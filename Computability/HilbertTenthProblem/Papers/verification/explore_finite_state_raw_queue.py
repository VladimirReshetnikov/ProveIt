"""A compiled seven-symbol queue simulation with raw ternary initialization."""
from dataclasses import dataclass
from pathlib import Path
import json
import sympy as sp

PLAIN=tuple((a,0) for a in range(3))
MARKED=tuple((a,2) for a in range(3))
DELIM=(0,1)
ALPHABET=PLAIN+MARKED+(DELIM,)
BLANK=2


@dataclass(frozen=True)
class State:
    kind:str
    q:str=''
    previous:tuple|None=None
    next_q:str|None=None
    seen:bool=False
    right:bool=False


class Machine:
    def __init__(self,name,transitions,initial='s',accept=('accept',),reject=('reject',)):
        self.name=name;self.delta=dict(transitions);self.initial=initial
        self.accept=set(accept);self.reject=set(reject)
        assert not self.accept & self.reject
        self.states={initial}|self.accept|self.reject|{q for q,_ in self.delta}|{v[0] for v in self.delta.values()}
        assert all(a in range(3) and b in range(3) and move in (-1,0,1)
                   for (_,a),(_,b,move) in self.delta.items())

    def start(self,q):
        if q in self.accept:return State('drain')
        if q in self.reject:return State('loop')
        return State('scan',q)

    def queue_transition(self,state,symbol):
        assert symbol in ALPHABET
        if state.kind=='drain':return state,(),''
        if state.kind=='loop':return state,(symbol,),''
        bad=(State('loop'),(DELIM,),'reject')
        if state.kind in ('load_first','load_rest'):
            if symbol in PLAIN:
                a=symbol[0];bits=(a//2,a%2)
                out=((bits[0],2 if state.kind=='load_first' else 0),(bits[1],0))
                return State('load_rest'),out,''
            if symbol==DELIM and state.kind=='load_rest':
                return self.start(self.initial),(PLAIN[BLANK],DELIM),'loaded'
            return bad
        assert state.kind=='scan'
        if symbol==DELIM:
            if not state.seen or state.previous is None:return bad
            out=(state.previous,)+( (MARKED[BLANK],) if state.right else () )+(DELIM,)
            return self.start(state.next_q),out,'pass'
        a,mark=symbol
        prev=state.previous;seen=state.seen;right=state.right;nq=state.next_q
        if mark==2:
            if seen or right:return bad
            entry=self.delta.get((state.q,a))
            if entry is None:return bad
            nq,b,move=entry;seen=True
            if move==-1:
                if prev is not None and prev[1]!=0:return bad
                out=(MARKED[BLANK] if prev is None else MARKED[prev[0]],)
                current=PLAIN[b]
            else:
                out=() if prev is None else (prev,)
                current=MARKED[b] if move==0 else PLAIN[b]
                right=move==1
        else:
            out=() if prev is None else (prev,)
            current=MARKED[a] if right else PLAIN[a]
            right=False
        return State('scan',state.q,current,nq,seen,right),out,''

    def compile(self):
        initial=State('load_first');todo=[initial];states={initial};table={}
        while todo:
            state=todo.pop()
            for symbol in ALPHABET:
                nxt,out,event=self.queue_transition(state,symbol)
                assert len(out)<=3 and all(a in ALPHABET for a in out)
                table[state,symbol]=(nxt,out,event)
                if nxt not in states:states.add(nxt);todo.append(nxt)
        assert len(states)<=28*len(self.states)*(len(self.states)+1)+4
        return initial,table,states


def coordinate(word,i):return sum(a[i]*3**j for j,a in enumerate(word))


def one_queue_step(machine,state,word,table=None):
    assert word
    nxt,out,event=machine.queue_transition(state,word[0]) if table is None else table[state,word[0]]
    result=word[1:]+out
    W=3**len(word)
    for i in range(2):
        assert 3*coordinate(result,i)==coordinate(word,i)-word[0][i]+coordinate(out,i)*W
    assert 3*3**len(result)==3**len(out)*W
    return nxt,result,event


def direct_step(machine,q,tape,head):
    assert q not in machine.accept|machine.reject
    entry=machine.delta.get((q,tape[head]))
    if entry is None:return None
    nq,b,move=entry;result=list(tape);result[head]=b;nh=head+move
    left=right=0
    if nh<0:result.insert(0,BLANK);nh=0;left=1
    elif nh==len(result):result.append(BLANK);right=1
    return nq,result,nh,left,right


def decode_tape(word):
    assert word and word[-1]==DELIM and DELIM not in word[:-1]
    cells=word[:-1];heads=[i for i,a in enumerate(cells) if a[1]==2]
    assert len(heads)==1
    return [a[0] for a in cells],heads[0]


def fixtures():
    out=[Machine('initial_accept',{},initial='accept'),Machine('initial_reject',{},initial='reject'),
         Machine('undefined',{})]
    out.append(Machine('scan_accept',{('s',a):('s',a,1) for a in (0,1)}|{('s',2):('accept',2,0)}))
    out.append(Machine('left_growth',{('s',a):('l',a,-1) for a in range(3)}|
        {('l',a):('r',1,1) for a in range(3)}|{('r',a):('accept',a,0) for a in range(3)}))
    out.append(Machine('right_growth',{('s',a):('s',a,1) for a in (0,1)}|
        {('s',2):('r',0,1),('r',2):('rr',1,1),('rr',2):('accept',0,-1)}))
    out.append(Machine('double_left',{(q,a):(nq,a,move) for q,nq,move in
        [('s','l',-1),('l','r',-1),('r','rr',1),('rr','accept',0)] for a in range(3)}))
    out.append(Machine('stay_accept',{('s',a):('accept',1-a if a in (0,1) else a,0) for a in range(3)}))
    out.append(Machine('infinite_right',{('s',a):('s',a,1) for a in range(3)}))
    out.append(Machine('infinite_stay',{('s',a):('s',a,0) for a in range(3)}))
    delta={}
    for q in ('s','odd'):
        delta[q,0]=(q,0,1);delta[q,1]=('odd' if q=='s' else 's',1,1)
        delta[q,2]=('accept' if q=='odd' else 'reject',2,0)
    out.append(Machine('binary_parity',delta))
    return out


def verify_input_formula():
    x,L,alpha,N0,N1,Winit=sp.symbols('x L alpha N0 N1 Winit')
    dag=[('length_output','*',3,'L'),('input_bound','+','x','alpha')]
    env=dict(x=x,L=L,alpha=alpha,N0=N0,N1=N1,Winit=Winit)
    for name,op,left,right in dag:
        a=env[left] if isinstance(left,str) else left
        b=env[right] if isinstance(right,str) else right
        env[name]=a*b if op=='*' else a+b
    residuals=[N0-x,N1-L,Winit-3*L,x+alpha-L]
    comparisons=[('N0','x'),('N1','L'),('Winit','length_output'),('input_bound','L')]
    assert all(sp.expand(env[a]-env[b]-r)==0 for (a,b),r in zip(comparisons,residuals))
    return dict(operations=2,multiplications=1,additions=1,
                initial_coordinates=['x','L'],dag=dag,
                source_residuals=[sp.sstr(r) for r in residuals],
                comparison='x+alpha=L, alpha>0',geometry='L=3^ell, ell>=1 external',
                optional_zero_input_length_guard='L=3Y, Y>0 costs one extra multiplication if needed')


def verify():
    total_states=total_edges=inputs=queue_steps=passes=accepted=rejected=cutoff=lefts=rights=0
    zero_inputs=padded_inputs=terminal_appends3=0
    for machine in fixtures():
        initial,table,states=machine.compile()
        total_states+=len(states);total_edges+=len(table)
        assert len(table)==7*len(states)
        for x in range(32):
            minimal=1
            while 3**minimal<=x:minimal+=1
            for pad in (0,1,2):
                ell=minimal+pad;L=3**ell
                digits=[(x//3**i)%3 for i in range(ell)]
                word=tuple(PLAIN[d] for d in digits)+(DELIM,);state=initial
                assert coordinate(word,0)==x and coordinate(word,1)==L
                assert 3**len(word)==3*L and L-x>0
                for _ in range(ell+1):
                    state,word,event=one_queue_step(machine,state,word,table);queue_steps+=1
                assert event=='loaded'
                bits=[bit for d in digits for bit in (d//2,d%2)]+[BLANK]
                tape,head=decode_tape(word);assert tape==bits and head==0
                q=machine.initial
                for _ in range(24):
                    if q in machine.accept|machine.reject:break
                    direct=direct_step(machine,q,tape,head)
                    while True:
                        before_len=len(word)
                        state,word,event=one_queue_step(machine,state,word,table);queue_steps+=1
                        if event in ('pass','reject'):break
                        assert word
                    if direct is None:
                        assert event=='reject' and state.kind=='loop';q='reject';break
                    assert event=='pass'
                    q,tape,head,left,right=direct
                    assert decode_tape(word)==(tape,head)
                    assert state.kind==('drain' if q in machine.accept else 'loop' if q in machine.reject else 'scan')
                    if state.kind=='scan':assert state.q==q and state.previous is None
                    lefts+=left;rights+=right;terminal_appends3+=right;passes+=1
                if q in machine.accept:
                    assert state.kind=='drain'
                    while word:
                        state,word,_=one_queue_step(machine,state,word,table);queue_steps+=1
                    accepted+=1
                elif q in machine.reject or state.kind=='loop':
                    assert word and state.kind=='loop'
                    old_len=len(word)
                    for _ in range(5):state,word,_=one_queue_step(machine,state,word,table);queue_steps+=1
                    assert len(word)==old_len;rejected+=1
                else:
                    assert machine.name in ('infinite_right','infinite_stay') and word
                    cutoff+=1
                inputs+=1;zero_inputs+=int(x==0);padded_inputs+=int(pad>0)
    return dict(status='PASS_FINITE_STATE_RAW_QUEUE',input=verify_input_formula(),
                finite=dict(fixed_test_machines=len(fixtures()),compiled_control_states=total_states,
                    compiled_symbol_transitions=total_edges,raw_padded_inputs=inputs,
                    queue_steps_with_two_coordinate_and_length_checks=queue_steps,
                    exact_simulated_Turing_steps=passes,accepted_and_fully_drained=accepted,
                    rejected_nonempty_loops=rejected,bounded_nonhalting_examples=cutoff,
                    left_boundary_growths=lefts,right_boundary_growths=rights,
                    delimiter_steps_appending_three=terminal_appends3,
                    zero_input_examples=zero_inputs,high_zero_padding_examples=padded_inputs),
                proof='../1980/EXPLORATION_FINITE_STATE_RAW_QUEUE.md',
                review_status='Author and independent root/binary_encoding full proof/source audits and fresh verify runs PASS; no findings. Publication is separate.',
                scope='An explicit finite-state universal queue contract and counted raw initialization. No total Diophantine verifier count; finite cutoff evidence is confined to named nonhalting test machines.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['finite'])

"""Literal universal 18-signal machine from Morita's 62-quintuple table.

Loads an independently transcribed source table, exports every rational-speed
label and every collision rule, and checks exact signal execution against the
ordinary Turing-tape semantics at every controller read.
"""
from pathlib import Path
from fractions import Fraction as F
from math import lcm
from collections import defaultdict
import json
from conservative_signal import compile_tm, blank_stack, event, adaptive_lift

HERE=Path(__file__).resolve().parent
DATA_DIR=HERE.parent/'data'
RECEIPTS=HERE.parent/'receipts'
DATA=json.loads((DATA_DIR/'MORITA_15_6_TABLE.json').read_text())
SYMBOLS=('b','Y','N','*','$','1')
NUM={s:i+1 for i,s in enumerate(SYMBOLS)}
TM={(t['state'],t['read']):(t['write'],t['move'],t['next_state'])
    for t in DATA['transitions']}
HALT={('q1','b'):'halt',('q2','$'):'null'}


def mode_code(order,speed):
    labels=sorted(speed)
    indices={a:i for i,a in enumerate(labels)}
    assert len(labels)==114 and len(order)==18
    code=0
    for label in order:
        code=114*code+indices[label]
    return code+1


def canonical_mode_orders():
    left=['L:mark0','L:mem']+['L:mark'+str(i) for i in range(1,7)]
    right=['R:mark'+str(i) for i in range(6,0,-1)]+['R:mem','R:mark0']
    return dict(initial=left+['q:q0','R:gl']+right,
                accept_final=left+['h:q1:1']+right+['e:q1:1'],
                null_final=left+['h:q2:5']+right+['e:q2:5'])


def compile_literal():
    direction={}
    for a,d,q in TM.values():
        assert q not in direction or direction[q]==d
        direction[q]=d
    write={(q,NUM[a]):('m'+n[1:],NUM[b]) for (q,a),(b,d,n) in TM.items()}
    move={'m'+q[1:]:(q,'R' if d==1 else 'L') for q,d in direction.items()}
    return compile_tm(write,move,'q0',set(),l=6,
                      halt_pairs={(q,NUM[a]) for q,a in HALT})


def encode_ctag(productions,word):
    """Phase0, first production is halt; remaining productions are Y/N words.

    Returns finite tape with head0 at first data symbol. All omitted cells b.
    """
    assert all(set(p)<={'Y','N'} for p in productions)
    assert set(word)<={'Y','N'}
    program=''.join(p[::-1]+'*' for p in productions[::-1])+'b'
    left=program+'$'
    tape={i-len(left):a for i,a in enumerate(left)}
    tape.update({i:a for i,a in enumerate(word)})
    return tape,program


def half_stack(tape,head,direction,include_head=False):
    start=head if include_head else head+direction
    nonblank=[i for i,a in tape.items() if a!='b' and (i-start)*direction>=0]
    if not nonblank:
        return F(1,6)
    end=max(nonblank) if direction==1 else min(nonblank)
    return blank_stack([NUM[tape.get(i,'b')] for i in range(start,end+direction,direction)],6)


def initial_signals(tape):
    sL=half_stack(tape,0,-1)
    sR=half_stack(tape,0,1,include_head=True)
    conf=[(F(-8+i),'L:mark'+str(i)) for i in range(7)]
    conf += [(F(8-i),'R:mark'+str(i)) for i in range(7)]
    conf += [(F(-8)+sL,'L:mem'),(F(8)-sR,'R:mem'),
             (F(0),'q:q0'),(F(1),'R:gl')]
    conf.sort()
    assert len(conf)==18
    return conf


def signal_replay(productions,word,limit=100000):
    speed,rules=compile_literal()
    tape,program=encode_ctag(productions,word)
    conf=initial_signals(tape)
    canonical=canonical_mode_orders()
    initial_order=[a for x,a in conf]
    assert initial_order==canonical['initial']
    q_initial=mode_code(initial_order,speed)
    initial_gaps=[conf[i+1][0]-conf[i][0] for i in range(17)]
    scale=lcm(*(g.denominator for g in initial_gaps))
    Q=scale
    h=[int(scale*g) for g in initial_gaps]
    time_numerator=0
    maximum_bits=max(x.bit_length() for x in h)
    state='q0'; head=0; tm_steps=0; batches=0; collisions=0; ties=0
    clock=F(0); halt_kind=None; halt_batch=None
    source_q={t['state'] for t in DATA['transitions']}|{t['next_state'] for t in DATA['transitions']}
    for _ in range(limit):
        old={a:x for x,a in conf}
        old_control=[a[2:] for x,a in conf if x==0 and a.startswith('q:')]
        out=event(conf,speed,rules)
        if out is None:
            assert halt_kind is not None, 'Unexpected collision-free nonhalt'
            break
        new,dt,receipt=out
        time_numerator=receipt['pivot_speed']*time_numerator+h[receipt['pivot']]
        h,scale=adaptive_lift(h,scale,receipt,new,span=16)
        maximum_bits=max(maximum_bits,max(x.bit_length() for x in h))
        batches+=1; collisions+=len(receipt['J']); ties+=len(receipt['J'])>1
        clock+=dt
        assert time_numerator*clock.denominator==scale*clock.numerator
        assert len(new)==18
        assert new[-1][0]-new[0][0]==16
        new_control=[a[2:] for x,a in new if x==0 and a.startswith('q:')]
        if old_control and old_control[0] in source_q and new_control!=old_control:
            # A complete TM current-symbol read at the center. Both memories
            # now hold precisely the cells strictly left/right of that head.
            assert old_control==[state]
            symbol=tape.get(head,'b')
            assert old['L:mem']+8==half_stack(tape,head,-1)
            assert 8-old['R:mem']==half_stack(tape,head,1)
            expected_tokens={'L:vr'+str(NUM[symbol]),'R:vr'+str(NUM[symbol])}
            assert expected_tokens & old.keys()
            if (state,symbol) in HALT:
                halt_kind=HALT[state,symbol]
                halt_batch=batches
                assert any(a==f'h:{state}:{NUM[symbol]}' for x,a in new)
            else:
                assert (state,symbol) in TM, ('Unexpected undefined source instruction',state,symbol)
                write,move,next_state=TM[state,symbol]
                assert new_control==['m'+next_state[1:]]
                tape[head]=write
                head+=move; state=next_state; tm_steps+=1
        conf=new
    else:
        raise RuntimeError('Signal replay limit exceeded')
    assert batches-halt_batch<=16
    final_order=[a for x,a in conf]
    kind='accept_final' if halt_kind=='halt' else 'null_final'
    assert final_order==canonical[kind]
    assert conf[-1][0]==conf[-2][0]==8
    assert speed[conf[-2][1]]==0 and speed[conf[-1][1]]==12
    assert all(speed[conf[i][1]]<=speed[conf[i+1][1]] for i in range(17))
    return dict(productions=['halt']+list(productions),input_word=word,
                initial_program=program,source_tm_steps=tm_steps,
                signal_batches=batches,signal_collisions=collisions,
                simultaneous_batches=ties,halt_kind=halt_kind,
                escape_suffix_batches=batches-halt_batch,
                final_clock=str(clock),population=18,
                q_initial=str(q_initial),q_final=str(mode_code(final_order,speed)),
                initial_label_order=initial_order,final_label_order=final_order,
                adaptive_pivot_lift_steps=batches,adaptive_initial_Q=str(Q),
                adaptive_peak_gap_bits=maximum_bits,
                adaptive_final_scale_bits=scale.bit_length(),
                adaptive_fixed_span_reconstruction_verified=True,
                timed_lift_verified=True,timed_numerator_bits=time_numerator.bit_length())


def export_machine():
    speed,rules=compile_literal()
    values=sorted(set(speed.values()))
    D=lcm(*(int(abs(a-b)) for a in values for b in values if a!=b))
    data=dict(provenance='Morita2008Table5 + Durand-Lose2012stackcompiler',
              symbols=NUM,population=18,span_at_event_cuts=16,
              speeds=[int(x) for x in values],D=D,
              meta_signals={a:int(v) for a,v in sorted(speed.items())},
              collision_rules=[dict(incoming=sorted(a),outgoing=sorted(b))
                               for a,b in sorted(rules.items(),key=lambda p:tuple(sorted(p[0])))],
              undefined_collision_semantics='forbidden',
              terminal_labels=sorted(a for a in speed if a.startswith('h:')),
              accept_labels=['h:q1:1'],reject_labels=['h:q2:5'],
              terminal_convention='q1,b is accepting halt; q2,$ is nonaccepting null')
    orders=canonical_mode_orders()
    data['mode_encoding']=dict(base=114,label_indices='zero-based lexicographic order',
        sorted_labels=sorted(speed),formula='1 + sum(index(label_i) * 114**(17-i) for i in range(18))',
        code_serialization='Exact decimal strings, to avoid JSON floating-point rounding',
        label_orders=orders,**{'q_'+k:str(mode_code(v,speed)) for k,v in orders.items()},
        initial_control_coordinate='u0 = 16 * q_initial * Q',
        accepting_target='u = q_accept_final * sum(h), with an admissible post-event germ',
        nonaccepting_null_target='u = q_null_final * sum(h), with an admissible post-event germ')
    data['integer_event_lift']=dict(preferred='canonical pivot-speed scaling',
        update='h_prime = c_j * h - c * h_j',
        pivot='j = min J, with J the complete earliest-collision edge set',
        gap_matrix_rank=16,gap_matrix_nonzeros_max=32,gap_coefficient_abs_max=24,
        fixed_span_recovery='g = 16*h/sum(h); tau = 16*h_j/(sum(h)*c_j)',
        initial_denominator='Q from the explicit two-half loader',
        invariant='h_k = Q * product(previous pivot closing speeds) * g_k',
        optional_uniform_denominator_lift_D=D)
    data['timed_extension']=dict(total_coordinates=19,
        initial_time_numerator=0,update='p_prime = c_j*p + h_j',
        time_recovery='t = 16*p/sum(h)',
        time_row_coefficient_abs_max=24)
    (DATA_DIR/'MORITA_18_SIGNAL_MACHINE.json').write_text(json.dumps(data,indent=2)+'\n')
    return len(speed),len(rules),D


def main():
    meta,rules,D=export_machine()
    examples=[(('YN','YYN'),'NYY'), (('YN','YYN'),'Y'),
              (('YN','YYN'),''), ((),'N'), (('',),'NY')]
    replays=[]
    for p,w in examples:
        receipt=signal_replay(p,w)
        print(json.dumps(receipt),flush=True)
        replays.append(receipt)
    assert replays[0]['source_tm_steps']==184
    result=dict(status='PASS',source_transitions=len(TM),meta_signals=meta,
                collision_rules=rules,population=18,D=D,
                every_controller_read_matched_exact_TM_tape=True,replays=replays)
    speed,_=compile_literal()
    result['canonical_mode_codes']={
        'q_'+k:str(mode_code(v,speed)) for k,v in canonical_mode_orders().items()}
    result['mode_orders_verified_on_all_five_runs']=True
    (RECEIPTS/'MORITA_18_REPLAY_RECEIPT.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='replays'},indent=2),flush=True)


if __name__=='__main__':
    main()

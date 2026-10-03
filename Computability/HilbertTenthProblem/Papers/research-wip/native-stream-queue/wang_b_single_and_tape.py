"""One complete native AND types a single tape head and reads/marks its cell.

This is a scalar relation, not an unbounded Wang-program certificate.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import native_binary_masked_selection63 as native


def build(mark=True):
    original, pairs, _ = native.source('and64_prescribed')
    _, auxiliary = native.domains('and64_prescribed')
    ports = {
        'q': ('*', 16, 'P'), 'scaled_A': ('*', 16, 'Hhat'),
        'padded_A': ('-', 'scaled_A', 4), 'scaled_B': ('*', 16, 'Mhat'),
        'padded_B': ('-', 'scaled_B', 6), 'scaled_Z': ('*', 16, 'Zhat'),
        'F3': ('-', 'scaled_Z', 8),
    }
    rows = {n: (op,a,b) for n,op,a,b in original}
    assert {n: rows[n] for n in ports} == ports
    for n, _, a, b in original:
        assert n in ports or not {'P','Hhat','Mhat','Zhat','scaled_A','scaled_B'} & {a,b}
    prefix = lambda x: 'and__'+x if isinstance(x,str) else x
    source = [
        ('tape_head', '+', 'tape_hat', 'head'),
        ('radix_partial', '+', 'tape_head', 'read_hat'),
        ('radix', '+', 'radix_partial', 'radix_slack'),
        ('radix16', '*', 16, 'radix'),
        ('head_region', '*', 'radix16', 'head'),
        ('and__q', '*', 'radix16', 'radix'),
        ('tape16', '*', 16, 'tape_hat'),
        ('input_A_sum', '+', 'tape16', 'head_region'),
        ('and__padded_A', '-', 'input_A_sum', 4),
        ('head16', '*', 16, 'head'),
        ('input_B_sum', '+', 'head_region', 'head16'),
        ('input_B_difference', '-', 'input_B_sum', 'radix16'),
        ('and__padded_B', '+', 'input_B_difference', 10),
        ('and__scaled_Z', '*', 16, 'read_hat'),
        ('and__F3', '-', 'and__scaled_Z', 8),
    ]
    source += [(prefix(n),op,prefix(a),prefix(b)) for n,op,a,b in original if n not in ports]
    comparisons = [(prefix(a),prefix(b)) for a,b in pairs]
    parameters = ['tape_hat','head']
    if mark:
        parameters += ['marked_hat']
        source += [('mark_lhs','+','marked_hat','read_hat'),
                   ('mark_rhs','+','tape_head',1)]
        comparisons += [('mark_lhs','mark_rhs')]
    aux = ['read_hat','radix_slack']+[prefix(n) for n in auxiliary]
    known = set(parameters+aux)
    for n,_,a,b in source:
        assert n not in known and all(not isinstance(v,str) or v in known for v in (a,b))
        known.add(n)
    assert all(a in known and b in known for a,b in comparisons)
    return dict(source=source,comparisons=comparisons,parameters=parameters,auxiliaries=aux,mark=mark)


def polynomial_source(packet):
    source = list(packet['source'])
    total = None
    for j,(a,b) in enumerate(packet['comparisons']):
        residual, square = f'residual{j}',f'square{j}'
        source += [(residual,'-',a,b),(square,'*',residual,residual)]
        if total is None: total=square
        else:
            nxt=f'sum{j}';source += [(nxt,'+',total,square)];total=nxt
    return source,total


def execute(source, values):
    e=dict(values)
    for n,op,a,b in source:
        x=e[a] if isinstance(a,str) else a
        y=e[b] if isinstance(b,str) else b
        e[n]=x*y if op=='*' else x+y if op=='+' else x-y
    return e


def ledger(packet):
    source,out=polynomial_source(packet)
    count=lambda rows:dict(Counter('M' if op=='*' else 'A' for _,op,_,_ in rows))
    degree={n:1 for n in packet['parameters']+packet['auxiliaries']}
    d=lambda x:degree[x] if isinstance(x,str) else 0
    for n,op,a,b in source:degree[n]=d(a)+d(b) if op=='*' else max(d(a),d(b))
    return dict(mark=packet['mark'],certificate_operations=len(packet['source']),
                certificate_split=count(packet['source']),comparisons=len(packet['comparisons']),
                positive_witnesses=len(packet['auxiliaries']),polynomial_operations=len(source),
                polynomial_split=count(source),degree_upper_bound=degree[out])


def wang_step(program, configuration, final_tape=None):
    """One physical set-of-cells step; final_tape enables the rejected shortcut."""
    pc, tape, head = configuration
    if pc == len(program): return None
    op, target = program[pc]
    current = tape if final_tape is None else final_tape
    if op == 'J': return (target if head in current else pc+1, tape, head)
    if op == 'M': return (pc+1, tape | {head}, head)
    assert op in ('L','R')
    return (pc+1, tape, head+(1 if op=='R' else -1))


def shifted_input_source():
    """Two initialization gates; head typing is a separate paid relation."""
    return [('shifted_input', '*', 'input', 'initial_head'),
            ('initial_tape_hat', '+', 'shifted_input', 1)]


def integer_step(program, configuration):
    """Independent integer-mask semantics on nonnegative tape coordinates."""
    pc, tape, head = configuration
    assert tape >= 0 and head > 0 and head & (head-1) == 0
    if pc == len(program): return None
    op, target = program[pc]
    if op == 'J': return (target if tape & head else pc+1, tape, head)
    if op == 'M': return (pc+1, tape+head-(tape & head), head)
    if op == 'R': return (pc+1, tape, head+head)
    assert op == 'L'
    if head == 1: raise ValueError('left move leaves the translated window')
    return (pc+1, tape, head//2)


def finite_window_checks():
    rng = random.Random(741242)
    programs = [[('L',None),('M',None),('R',None),('J',5),('M',None),('R',None)],
                [('R',None),('M',None),('L',None),('J',4),('M',None)]]
    for _ in range(30):
        length = rng.randrange(4,11)
        programs.append([(op, rng.randrange(length) if op == 'J' else None)
                         for op in (rng.choice('LRMJ') for _ in range(length))])
    translated = steps = halts = negative_head_runs = 0
    instructions = Counter()
    for program in programs:
        for _ in range(4):
            x = rng.randrange(1,256)
            physical = [(0,{j for j in range(x.bit_length()) if (x>>j)&1},0)]
            for _ in range(64):
                nxt = wang_step(program,physical[-1])
                if nxt is None: break
                instructions[program[physical[-1][0]][0]] += 1
                physical.append(nxt)
            halts += physical[-1][0] == len(program)
            minimum = min(head for _,_,head in physical)
            negative_head_runs += minimum < 0
            for padding in (0,3):
                offset = max(0,-minimum)+padding
                H0 = 1<<offset
                initial = execute(shifted_input_source(),dict(input=x,initial_head=H0))
                assert initial['initial_tape_hat'] == x*H0+1
                encoded = [(pc,sum(1<<(j+offset) for j in tape),1<<(head+offset))
                           for pc,tape,head in physical]
                assert encoded[0] == (0,initial['initial_tape_hat']-1,H0)
                for (pc,T,H),(physical_pc,cells,h) in zip(encoded,physical):
                    assert pc == physical_pc and H.bit_length()-1-offset == h
                    recovered = {j-offset for j in range(T.bit_length()) if (T>>j)&1}
                    assert recovered == cells
                    C = T&H
                    P = 1<<(T+1+H+C+1).bit_length()
                    assert P-(T+1+H+C+1)>0
                    assert ((T+P*H)&(H+P*(H-1))) == C
                for before,after in zip(encoded,encoded[1:]):
                    assert integer_step(program,before) == after
                    steps += 1
                if physical[-1][0] == len(program):
                    assert integer_step(program,encoded[-1]) is None
                translated += 1
    assert set(instructions) == set('LRMJ') and negative_head_runs > 0 and halts > 0
    try:
        integer_step([('L',None)],(0,0,1))
        assert False,'a positive head cannot halve below 1'
    except ValueError:
        pass
    return dict(physical_runs=len(programs)*4,translated_runs=translated,
                translated_steps=steps,halting_physical_runs=halts,
                physical_runs_visiting_negative_cells=negative_head_runs,
                physical_instruction_counts=dict(sorted(instructions.items())),
                offsets_per_run=2,initialization_source=shifted_input_source(),
                initial_head_typing='Separate paid initial head/read instance; not supplied by the two gates.',
                scope='Finite literal-Wang-input trace translation; no uniform history or TM input encoding.')


def verify():
    rng=random.Random(74124)
    audits=0
    os,oc,_=native.source('and64_prescribed');_,oa=native.domains('and64_prescribed')
    records=[]
    for mark in (False,True):
        p=build(mark);records.append(ledger(p));src,out=polynomial_source(p)
        for j in range(128):
            positive=j<64
            values={n:rng.randrange(1,8) if positive else rng.randrange(-5,6)
                    for n in p['parameters']+p['auxiliaries']}
            e=execute(src,values)
            T,H,C=values['tape_hat']-1,values['head'],values['read_hat']-1
            P=values['tape_hat']+H+values['read_hat']+values['radix_slack']
            supplied={n:values['and__'+n] for n in oa}
            supplied.update(P=P*P,Hhat=T+P*H+1,Mhat=H+P*(H-1)+1,Zhat=C+1)
            ref=native.parent.execute(os,supplied)
            expected=[ref[a]-ref[b] for a,b in oc]
            if mark:expected += [values['marked_hat']+values['read_hat']-values['tape_hat']-H-1]
            assert [e[a]-e[b] for a,b in p['comparisons']]==expected
            assert e[out]==sum(x*x for x in expected)
            for n in ('q','padded_A','padded_B','F3'):assert e['and__'+n]==ref[n]
            if positive:
                assert all(supplied[n]>0 for n in ('P','Hhat','Mhat','Zhat'))
                assert P>max(T,H,C) and P>=4
            audits+=1
    low_cases=0
    for T in range(32):
        for H in range(1,32):
            for C in range(32):
                P=1<<(T+H+C+3).bit_length()
                joined=((T+P*H)&(H+P*(H-1)))==C
                assert joined==((H&(H-1))==0 and C==(T&H))
                if joined:assert T+H-C==T|H
                low_cases+=1
    extensions=0
    for T in range(64):
        for h in range(8):
            H=1<<h;C=T&H
            P=1<<(T+1+H+C+1).bit_length()
            beta=P-(T+1+H+C+1)
            assert beta>0 and P==T+1+H+C+1+beta
            assert ((T+P*H)&(H+P*(H-1)))==C
            assert max(T+P*H,H+P*(H-1),C)<P*P
            assert (T|H)+1+(C+1)==(T+1)+H+1
            extensions+=1
    # Exact lasso: [J(3),M,J(2),M] on an initially empty tape.
    # Its real execution reaches (instruction2,tape{0},head0) and self-loops.
    program=[('J',3),('M',None),('J',2),('M',None)]
    real=[(0,set(),0),(1,set(),0),(2,{0},0),(2,{0},0)]
    for before,after in zip(real,real[1:]):assert wang_step(program,before)==after
    # A final-tape read at instruction0 would instead allow 0->3->HALT,
    # with the final1 justified only by that future mark.
    future=[(0,set(),0),(3,set(),0),(4,{0},0)]
    for before,after in zip(future,future[1:]):
        assert wang_step(program,before,final_tape=future[-1][1])==after
    assert wang_step(program,future[-1]) is None
    save_trace=lambda trace:[dict(pc=pc,marked_cells=sorted(tape),head=head) for pc,tape,head in trace]
    assert records[0]['certificate_operations']==72 and records[0]['polynomial_operations']==119
    assert records[1]['certificate_operations']==74 and records[1]['polynomial_operations']==124
    p=build();source,out=polynomial_source(p)
    return dict(status='PASS_WANG_B_SINGLE_AND_TAPE',ledgers=records,
                canonical_native_residual_and_SOS_identities=audits,signed_cases=audits//2,
                exact_low_block_cases=low_cases,positive_outer_extensions=extensions,
                finite_window_translation=finite_window_checks(),
                future_read_obstruction=dict(program=['J(3)','M','J(2)','M'],real_lasso=save_trace(real),
                                             relaxed_future_read_path=save_trace(future)),
                example=dict(source=source,output=out,comparisons=p['comparisons'],
                             parameters=p['parameters'],auxiliaries=p['auxiliaries']),
                scope='Complete scalar head/read/mark relation, not a uniform Wang-program '
                      'history or a new universal arithmetic bound. Outer fixtures do not '
                      'materialize positive native Pell witnesses.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['ledgers'])

"""Uniform fixed Wang B instruction control over a paid tape/motion history.

Programs use labels1..m, ('J',target) jumps on a read1, and halt at m+1.
Literal positive binary Wang input is paid; no TM-to-Wang morphism is inferred.
"""
import argparse
from collections import Counter
import json
from itertools import product
from pathlib import Path
import random

import wang_b_packed_motion as motion
import native_binary_positive_scale as positive_scale
import native_binary_computed_fields as fields
import native_binary_norm_units as units

DEFAULT = ('M', 'R', ('J', 1), 'L', ('J', 6), 'M')
PARAMETERS = list(motion.PARAMETERS)


def normalize(program):
    result = []
    assert len(program) > 0
    for instruction in program:
        if isinstance(instruction, str):
            assert instruction in ('M', 'L', 'R')
            result.append(instruction)
        else:
            assert len(instruction) == 2 and instruction[0] == 'J'
            assert isinstance(instruction[1], int) and 1 <= instruction[1] <= len(program)
            result.append(('J', instruction[1]))
    return tuple(result)


def edges(program):
    result = []
    for index, instruction in enumerate(program, 1):
        choices = [(index+1, instruction, None)] if isinstance(instruction, str) else [
            (index+1, 'J', 0), (instruction[1], 'J', 1)]
        for target, action, read in choices:
            result.append(dict(source=index, target=target, action=action, read=read))
    return result


def power(g, P, exponent):
    assert exponent >= 1
    value = P
    for bit in bin(exponent)[3:]:
        value = g.emit('*', value, value, 'power_square')
        if bit == '1':
            value = g.emit('*', value, P, 'power_multiply')
    return value


def compile_raw(program=DEFAULT, literal_input=False):
    program = normalize(program)
    table = edges(program)
    K = len(table)
    jump = any(e['action'] == 'J' for e in table)
    radix_factor = 1 << (max(16, K+2)-1).bit_length()
    parent = motion.build()
    interface = parent['interfaces']
    stop = next(i for i, row in enumerate(parent['source']) if row[0].startswith('input_H_'))
    g = motion.parent.Gates()
    g.source = list(parent['source'][:stop])
    half = interface['Bhalf']
    assert stop == 56 and next(row for row in g.source if row[0] == half) == (half, '*', 4, interface['D'])
    g.source = [(n, op, radix_factor//2, b) if n == half else (n, op, a, b)
                for n, op, a, b in g.source]
    for n, op, a, b in g.source:
        key = (op, *sorted((a, b), key=repr)) if op in ('+', '*') else (op, a, b)
        g.cache[key] = n
    emit = g.emit
    summation = lambda terms, label: g.sum(terms, label) if terms else 0
    D, B, Bm1, J, P, H = (interface[n] for n in ('D', 'B', 'Bm1', 'J', 'P', 'H'))
    E = [emit('-', f'edge{i}_hat', 1, 'edge') for i in range(K)]
    partition = summation(E, 'edge_partition')
    action = {a: summation([e for e, row in zip(E, table) if row['action'] == a], 'action_'+a)
              for a in ('M', 'L', 'R', 'J')}
    current = summation([emit('*', row['source'], e, 'instruction') for e, row in zip(E, table)], 'current')
    following = summation([emit('*', row['target'], e, 'target') for e, row in zip(E, table)], 'following')
    control_left = emit('+', emit('*', B, following, 'shift_control'), 1, 'control_left')
    control_right = emit('+', current, emit('*', P, len(program)+1, 'halt_control'), 'control_right')
    ah = [H, interface['T'], H, interface['C'], interface['I'], interface['T'], interface['G'],
          interface['Move'], interface['L'], H, H, interface['I']]
    am = [interface['G'], H, interface['mark_mask'], interface['mark_mask'], J,
          interface['range_mask'], interface['range_mask'], J, interface['Move'],
          interface['move_mask'], interface['left_mask'], interface['Move']]
    az = [0, interface['C'], interface['W'], interface['V'], interface['I'], interface['T'],
          interface['G'], interface['Move'], interface['L'], interface['MH'], interface['LH'], 0]
    ah += E; am += [J]*K; az += E
    bound = interface['global_bound']
    branch_output = taken = jump_mask = taken_mask = None
    if jump:
        taken = summation([e for e, row in zip(E, table) if row['read'] == 1], 'taken_rows')
        jump_mask = emit('*', Bm1, action['J'], 'jump_mask')
        taken_mask = emit('*', Bm1, taken, 'taken_mask')
        branch_output = emit('-', 'branch_output_hat', 1, 'branch_output')
        bound = emit('+', bound, 'branch_output_hat', 'branch_bound')
        ah += [interface['C'], H]; am += [jump_mask, taken_mask]; az += [branch_output]*2
    lane_count = len(ah)
    joined = [g.pack(coefficients, P, label) for coefficients, label in zip((ah, am, az), ('input_H', 'input_M', 'output_Z'))]
    native_scale = emit('*', B, power(g, P, lane_count), 'native_scale')
    native = motion.native
    ns, native_pairs, _ = native.source('and64_prescribed')
    pre = 'native__'
    name = lambda x: pre+x if isinstance(x, str) else x
    source = g.source+[(pre+'q', '*', 16, native_scale), (pre+'scaled_A', '*', 16, joined[0]),
        (pre+'padded_A', '+', pre+'scaled_A', 12), (pre+'scaled_B', '*', 16, joined[1]),
        (pre+'padded_B', '+', pre+'scaled_B', 10), (pre+'scaled_Z', '*', 16, joined[2]),
        (pre+'F3', '+', pre+'scaled_Z', 8)]
    source += [(name(n), op, name(a), name(b)) for n, op, a, b in ns[7:]]
    comparisons = [(bound, P)]+parent['comparisons'][1:3]
    comparisons += [(partition, J), (interface['I'], action['M']),
                    (interface['L'], action['L']), (interface['R'], action['R']),
                    (control_left, control_right)]
    comparisons += [(name(a), name(b)) for a, b in native_pairs]
    aux = parent['auxiliaries']+[f'edge{i}_hat' for i in range(K)]+(['branch_output_hat'] if jump else [])
    params = list(PARAMETERS)
    if literal_input:
        source = [('literal_input_product', '*', 'input', 'initial_head'),
                  ('initial_tape_hat', '+', 'literal_input_product', 1)]+source
        params = ['input']
        aux += ['final_tape_hat', 'initial_head', 'final_head']
    packet = positive_scale.metadata(dict(source=source, comparisons=comparisons, parameters=params,
        auxiliaries=aux, program=program, edges=table, literal_input=literal_input,
        radix_factor=radix_factor, lane_count=lane_count, outer_equations=8,
        interfaces=dict(interface, global_bound=bound, joined_H=joined[0], joined_M=joined[1],
                        joined_Z=joined[2], native_scale=native_scale, edge_words=E,
                        current_control=current, following_control=following,
                        control_left=control_left, control_right=control_right,
                        partition=partition, branch_output=branch_output, taken=taken,
                        jump_mask=jump_mask, taken_mask=taken_mask)))
    positive_scale.checked_source(source, params, aux)
    assert packet['equations'] == 24 and packet['witnesses'] == 35+K+int(jump)+3*literal_input
    return packet


def build(program=DEFAULT, literal_input=False, form='units'):
    assert form in ('raw', 'scaled', 'projected', 'units')
    packet = compile_raw(program, literal_input)
    if form != 'raw':
        packet = positive_scale.rewrite(packet, 'native__')
    if form in ('projected','units'):
        packet = fields.rewrite(packet, prefix='native__')
    if form == 'units':
        packet = units.rewrite(packet,normalized=True)
    return dict(packet, form=form)


def polynomial_source(packet):
    return units.polynomial_source(packet) if packet.get('native_norm_units') else motion.polynomial_source(packet)


def ledger(packet):
    return units.ledger(packet) if packet.get('native_norm_units') else motion.ledger(packet)


execute = motion.execute


def independent_raw(packet, values):
    """Direct packing and canonical native invocation; no emitted outer gates."""
    program, table = packet['program'], packet['edges']
    v = dict(values)
    if packet['literal_input']:
        v['initial_tape_hat'] = v['input']*v['initial_head']+1
    words = {w: v[w+'_hat']-1 for w in motion.WORDS}
    D = sum(v[n] for n in PARAMETERS)+v['height_slack']
    B = packet['radix_factor']*D
    J = sum(v[n+'_hat']-1 for n in ('I', 'L', 'R', 'Stay'))
    P = (B-1)*J+1
    H = words['G']+J
    Move = words['L']+words['R']
    mask = lambda S: (B-1)*S
    range_mask = (D-1)*J
    aa = [H, words['T'], H, words['C'], words['I'], words['T'], words['G'], Move,
          words['L'], H, H, words['I']]
    mm = [words['G'], H, mask(words['I']), mask(words['I']), J, range_mask, range_mask,
          J, Move, mask(Move), mask(words['L']), Move]
    zz = [0, words['C'], words['W'], words['V'], words['I'], words['T'], words['G'],
          Move, words['L'], words['MH'], words['LH'], 0]
    E = [v[f'edge{i}_hat']-1 for i in range(len(table))]
    action = {a: sum(e for e, row in zip(E, table) if row['action'] == a) for a in ('M', 'L', 'R', 'J')}
    now = sum(row['source']*e for row, e in zip(table, E))
    nxt = sum(row['target']*e for row, e in zip(table, E))
    bound = J+sum(v[w+'_hat'] for w in motion.WORDS)+v['global_bound']
    aa += E; mm += [J]*len(E); zz += E
    if 'branch_output_hat' in v:
        taken = sum(e for e, row in zip(E, table) if row['read'] == 1)
        Z = v['branch_output_hat']-1
        aa += [words['C'], H]; mm += [mask(action['J']), mask(taken)]; zz += [Z, Z]
        bound += v['branch_output_hat']
    pack = lambda row: sum(a*P**i for i, a in enumerate(row))
    A, M, Z = map(pack, (aa, mm, zz))
    residuals = [bound-P,
        B*(words['T']+words['W']-words['V'])+v['initial_tape_hat']-
            (words['T']+P*v['final_tape_hat']-(P-1)),
        B*(H+words['MH']-words['LH'])+v['initial_head']-
            (H+P*v['final_head']+(B//2)*words['LH']),
        sum(E)-J, words['I']-action['M'], words['L']-action['L'], words['R']-action['R'],
        B*nxt+1-now-P*(len(program)+1)]
    nv = dict(P=B*P**len(aa), Hhat=A+1, Mhat=M+1, Zhat=Z+1,
              **{n: v['native__'+n] for n in motion.native.domains('and64_prescribed')[1]})
    ns, pairs, _ = motion.native.source('and64_prescribed')
    env = execute(ns, nv)
    residuals += [env[a]-env[b] for a, b in pairs]
    return residuals, (A, M, Z), nv


def run(program, tape, head, limit=200):
    """Finite literal Wang execution, recording current pre-action reads."""
    program = normalize(program)
    assert tape >= 0 and head > 0 and head & (head-1) == 0
    rows = []; pc = 1
    while pc <= len(program) and len(rows) < limit:
        instruction = program[pc-1]
        read = int(bool(tape & head))
        action = instruction if isinstance(instruction, str) else 'J'
        following = pc+1 if action != 'J' or not read else instruction[1]
        rows.append(dict(pc=pc, next=following, tape=tape, head=head, read=read, action=action))
        if action == 'M': tape |= head
        elif action == 'L':
            if head == 1: return dict(halted=False, boundary=True, rows=rows)
            head //= 2
        elif action == 'R': head *= 2
        pc = following
    return dict(halted=pc == len(program)+1, boundary=False, rows=rows, final_tape=tape, final_head=head)


def positive_history(program, tape, head, limit=200, literal_input=False):
    packet = compile_raw(program, literal_input)
    trace = run(program, tape, head, limit)
    assert trace['halted'] and trace['rows']
    if literal_input:
        assert tape > 0 and tape % head == 0
    rows = trace['rows']; n = len(rows)
    params = dict(initial_tape_hat=tape+1, final_tape_hat=trace['final_tape']+1,
                  initial_head=head, final_head=trace['final_head'])
    D = 16
    while D <= max([sum(params.values())]+[row[x] for row in rows for x in ('tape', 'head')]+[trace['final_tape'], trace['final_head']]):
        D *= 2
    B = packet['radix_factor']*D
    P = B**n; J = (P-1)//(B-1)
    pack = lambda seq: sum(a*B**i for i, a in enumerate(seq))
    v = {w: [] for w in motion.WORDS}; stay=[]
    E = [[] for _ in packet['edges']]; branch=[]
    for row in rows:
        T,H,C = row['tape'],row['head'],row['tape']&row['head']
        I,L,R = (int(row['action'] == a) for a in ('M','L','R'))
        vals = dict(T=T,G=H-1,C=C,I=I,W=I*H,V=I*C,L=L,R=R,MH=(L+R)*H,LH=L*H)
        for w in v:v[w].append(vals[w])
        stay.append(int(row['action']=='J'));branch.append(C if row['action']=='J' else 0)
        for dest,e in zip(E,packet['edges']):
            dest.append(int(e['source']==row['pc'] and (e['read'] is None or e['read']==row['read'])))
    values = dict(params,height_slack=D-sum(params.values()),Stay_hat=pack(stay)+1,
                  **{w+'_hat':pack(seq)+1 for w,seq in v.items()},
                  **{f'edge{i}_hat':pack(seq)+1 for i,seq in enumerate(E)})
    if any(e['action']=='J' for e in packet['edges']):values['branch_output_hat']=pack(branch)+1
    values['global_bound']=P-J-sum(values[w+'_hat'] for w in motion.WORDS)-values.get('branch_output_hat',0)
    assert values['global_bound'] >= (packet['radix_factor']-8)*D*J-10 > 0
    if literal_input:
        values['input']=tape//head;del values['initial_tape_hat']
    values.update({'native__'+a:1 for a in motion.native.domains('and64_prescribed')[1]})
    assert min(values.values())>0
    return values,trace


def raw_lift(packet, values):
    if packet.get('native_norm_units'):
        assert packet['normalized_strong']
        values=units.lift_to_parent(packet,values);packet=packet['normalized_parent']
        values=units.lift_to_parent(packet,values);packet=packet['unit_parent']
    if packet.get('native_computed_fields'):
        values=fields.lift_to_parent(packet,values);packet=packet['computed_parent']
    if packet.get('native_positive_scale'):
        values=positive_scale.lift_to_parent(packet,values)
    return values


def unit_raw_oracle(packet,values,raw,residuals,restored):
    """Full finalizer from the independently assembled RAW comparison oracle.

    The strong normalization cancels the intermediate auxiliary-coefficient
    correction, so the normalized auxiliary factor is 1+raw auxiliary residual.
    """
    p='native__'
    old=packet['normalized_parent'];projected=old['unit_parent'];scaled=projected['computed_parent']
    rr=dict(zip(raw['comparisons'],residuals))
    r=lambda a,b:rr[(p+a,p+b)]
    a,c=restored[p+'a'],restored[p+'c']
    Delta=a*a+4*a+3
    N=values[p+'f']**2-Delta*(values[p+'i']*c*c)**2
    fs=[1+r('L15','R15'),1+r('L17','P17'),1-4*r('L9','R9'),1-r('bs_q','q'),N]
    assert r('ic22','R16')==Delta*(1-N)
    removed=set(projected['computed_removed_comparisons'])|set(old['norm_removed_comparisons'])
    removed.add(scaled['positive_scale_removed_comparison'])
    removed.add(packet['removed_strong_comparison'])
    rs=[v for pair,v in zip(raw['comparisons'],residuals) if pair not in removed]
    product=1
    for f in fs:product*=f
    return product*(1+sum(r*r for r in rs))-1,fs,rs


def bounds(packet):
    K=len(packet['edges']);j=sum(e['read']==1 for e in packet['edges']);delta=int(j>0)
    L=packet['lane_count'];mu=L.bit_length()-1+L.bit_count()-1
    e=2 if packet['literal_input'] else 1
    nu=e+1;sigma=e+L*nu;zeta=(L-1)*nu+1
    C=115+7*K+6*L+mu+delta*(j+3)+2*packet['literal_input']
    if packet['form']=='units':
        C+=5;degree=72*sigma+13*zeta+39
        actual=units.degree_bound(packet)['degree_upper_bound']
    else:
        degree=24*sigma+4*zeta+12 if packet['form']=='projected' else 12*sigma+16
        actual=motion.degree_bound(packet)
    assert packet['operations']<=C and actual<=degree
    return dict(certificate_upper_bound=C,degree_upper_bound=degree,power_chain_multiplications=mu)


def control_audit():
    checked=valid=0
    for program in [('M',),(('J',1),),('M',('J',1),'R'),(('J',3),'L','M')]:
        table=edges(program);B=128
        for duration in range(1,5):
            for sequence in product(table,repeat=duration):
                current=sum(r['source']*B**i for i,r in enumerate(sequence))
                following=sum(r['target']*B**i for i,r in enumerate(sequence))
                arithmetic=B*following+1==current+B**duration*(len(program)+1)
                chronological=(sequence[0]['source']==1 and sequence[-1]['target']==len(program)+1 and
                    all(a['target']==b['source'] for a,b in zip(sequence,sequence[1:])))
                assert arithmetic==chronological
                checked+=1;valid+=arithmetic
    return dict(exhaustive_edge_sequences=checked,chronological_accepting_sequences=valid,
                scope='Exact controller transport, not a tape-read assertion for arbitrary sequences.')


def rejected_future_read():
    # The actual program loops at label3 after marking, while an illicit
    # final-tape read would permit the path1->4->halt.
    program=(('J',4),'M',('J',3),'M');packet=compile_raw(program)
    trace=run(program,0,1,5)
    assert not trace['halted'] and [r['pc'] for r in trace['rows']]==[1,2,3,3,3]
    assert trace['rows'][2]==trace['rows'][3]
    D=16;B=packet['radix_factor']*D;P=B*B;J=B+1
    raw=dict(T=0,G=0,C=0,I=B,W=B,V=0,L=0,R=0,MH=0,LH=0)
    values={w+'_hat':raw[w]+1 for w in motion.WORDS}
    values.update(initial_tape_hat=1,final_tape_hat=2,initial_head=1,final_head=1,
                  height_slack=D-5,Stay_hat=2,branch_output_hat=2)
    for i,e in enumerate(packet['edges']):
        values[f'edge{i}_hat']=1+(1 if e['source']==1 and e['read']==1 else
                                  B if e['source']==4 else 0)
    values['global_bound']=P-J-sum(values[w+'_hat'] for w in motion.WORDS)-2
    values.update({'native__'+a:1 for a in motion.native.domains('and64_prescribed')[1]})
    assert min(values.values())>0
    rr,words,_=independent_raw(packet,values)
    assert rr[:8]==[0]*8
    lane=12+len(packet['edges'])
    assert (words[0]&words[1])-words[2]==-P**lane
    return dict(program=program,forged_control=[1,4,5],actual_lasso=[1,2,3,3],
                failed_selected_current_read_lane=lane,
                scope='Every outer comparison and all other bit lanes hold; not a full Pell zero.')


def verify():
    rng=random.Random(202610071)
    programs=[('M',),('R',),('L',),(('J',1),),DEFAULT,
              ('M',('J',4),'R','L'),('R',('J',1),'M'),tuple(['M']*19)]
    ledgers=[];identities=positive=signed=half_integral=0
    for program in programs:
        for literal in (False,True):
            raw=compile_raw(program,literal)
            for form in ('raw','scaled','projected','units'):
                packet=build(program,literal,form);source,out=polynomial_source(packet)
                for case in range(16):
                    pos=case<8
                    values={n:rng.randrange(1,6) if pos else rng.randrange(-4,5)
                            for n in packet['parameters']+packet['auxiliaries']}
                    env=execute(source,values);restored=raw_lift(packet,values)
                    rr,words,nv=independent_raw(raw,restored)
                    if form=='units':
                        half_integral+=pos and restored['native__tau'].denominator==2
                        expected,fs,rs=unit_raw_oracle(packet,values,raw,rr,restored)
                        assert env[out]==expected
                        assert fs==[env[n] for n in packet['unit_factors']]
                        at=lambda v:env[v] if isinstance(v,str) else v
                        assert rs==[at(a)-at(b) for a,b in packet['comparisons'][:-1]]
                        ss,so=units.polynomial_source(packet,sum_of_squares=True)
                        product=1
                        for f in fs:product*=f
                        assert execute(ss,values)[so]==(product-1)**2+sum(r*r for r in rs)
                    else:
                        assert env[out]==sum(x*x for x in rr)
                    if pos:
                        assert min(restored.values())>0 and min(words)>=0 and nv['P']>=1
                        positive+=1
                    else:signed+=1
                    identities+=1
                ledgers.append(dict(program=program,literal_input=literal,form=form,edges=len(packet['edges']),
                    lanes=packet['lane_count'],radix_factor=packet['radix_factor'],ledger=ledger(packet),bounds=bounds(packet)))
                fields.source_closure(packet)
    histories=steps=branch0=branch1=one=unit_transfers=0
    for program in programs:
        for case in range(16):
            head=1<<rng.randrange(2,6);x=rng.randrange(1,64)
            trace=run(program,x*head,head,80)
            if not trace['halted']:continue
            for literal in (False,True):
                raw=compile_raw(program,literal)
                values,trace=positive_history(program,x*head,head,80,literal)
                rr,words,nv=independent_raw(raw,values)
                assert rr[:8]==[0]*8 and words[0]&words[1]==words[2] and max(words)<nv['P']
                env=execute(raw['source'],values)
                assert [env[a] if isinstance(a,str) else a for a,b in raw['comparisons'][:8]]==[
                       env[b] if isinstance(b,str) else b for a,b in raw['comparisons'][:8]]
                if case<2:
                    unit_packet=build(program,literal,'units')
                    unit_values={n:values[n] for n in unit_packet['parameters']+unit_packet['auxiliaries'] if n in values}
                    unit_values['native__tau_gap']=3
                    transported=raw_lift(unit_packet,unit_values)
                    assert min(transported.values())>0 and all(int(v)==v for v in transported.values())
                    tr,tw,tn=independent_raw(raw,transported)
                    assert tr[:8]==[0]*8 and tw==words and tn['P']==nv['P']
                    unit_transfers+=1
                histories+=1;steps+=len(trace['rows']);one+=len(trace['rows'])==1
                branch0+=sum(r['action']=='J' and r['read']==0 for r in trace['rows'])
                branch1+=sum(r['action']=='J' and r['read']==1 for r in trace['rows'])
    return dict(status='PASS_WANG_B_PACKED_PROGRAM',ledgers=ledgers,
        source_checks=dict(full_output_identities=identities,signed=signed,positive=positive,
                           positive_half_integral_offzero_root_lifts=half_integral),
        outer_histories=dict(histories=histories,steps=steps,duration_one=one,jump_zero=branch0,jump_one=branch1,
                            normalized_unit_outer_transfers=unit_transfers,
            scope='Actual halted program traces; native coordinates are placeholders, not full Pell zeros.'),
        controller_transport=control_audit(),rejected_future_read=rejected_future_read(),
        default={form:ledger(build(form=form)) for form in ('raw','scaled','projected','units')},
        literal_input_default={form:ledger(build(literal_input=True,form=form)) for form in ('raw','scaled','projected','units')},
        scope='Complete fixed-program nonempty Wang halting history, including literal positive binary input and paid spatial shift. No TM-to-Wang encoding or numerical universal program is instantiated.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert result==json.loads(path.read_text()),'receipt mismatch'
    print(result['status']);print(result['default']);print(result['literal_input_default']);print(result['outer_histories'])

#!/usr/bin/env python3
"""Independent source semantics and packed outer-history checks, stdlib only.

No upstream Python is imported or executed. This checks finite arithmetic
examples; complete positive native Pell tuples are deliberately not fabricated.
"""
from collections import Counter
import argparse
import copy
import hashlib
import json
from pathlib import Path
import random

ROOT = Path(__file__).resolve().parent

def need(ok, why):
    if not ok:
        raise ValueError(why)

def execute(rows, values, modulus=None):
    env = dict(values)
    for name, op, a, b in rows:
        left = env[a] if type(a) is str else a
        right = env[b] if type(b) is str else b
        value = left + right if op == '+' else left - right if op == '-' else left * right
        env[name] = value if modulus is None else value % modulus
    return env

def residuals(packet, env):
    at = lambda x: env[x] if type(x) is str else x
    return [at(a) - at(b) for a,b in packet['comparisons']]

def instruction_step(instructions, halt, state, payload):
    if state == halt:
        return None
    applicable = []
    for src, dst, op, counter in instructions:
        if src != state:
            continue
        p = (2,3)[counter]
        if op in ('dec','positive') and payload % p:
            continue
        if op == 'zero' and payload % p == 0:
            continue
        following = payload*p if op == 'inc' else payload//p if op == 'dec' else payload
        duration = (108*payload + 96*following if op == 'inc' else 96*payload + 108*following if op == 'dec' else 192*payload) + 8
        applicable.append((dst,following,duration))
    need(len(applicable) <= 1, 'Unique source step')
    return applicable[0] if applicable else None

def trace(instructions, entry, halt, payload, limit=100):
    states = [(entry,payload)]
    durations = []
    seen = set()
    while states[-1][0] != halt:
        state, value = states[-1]
        if (state,value) in seen:
            return states,durations,'cycle'
        seen.add((state,value))
        step = instruction_step(instructions,halt,state,value)
        if step is None:
            return states,durations,'stuck'
        next_state, next_value, elapsed = step
        states.append((next_state,next_value))
        durations.append(elapsed)
        if len(durations) == limit and next_state != halt:
            return states,durations,'prefix'
    return states,durations,'halt'

def clean(instructions,entry,halt):
    need(all(dst != entry and src != halt for src,dst,_,_ in instructions), 'Fresh entry, terminal halt')
    reverse_op = {'inc':'dec','dec':'inc','nop':'nop','zero':'zero','positive':'positive'}
    result = [[('F',src),('F',dst),op,k] for src,dst,op,k in instructions]
    result += [[('B',dst),('B',src),reverse_op[op],k] for src,dst,op,k in instructions]
    result += [[('F',halt),('B',halt),'nop',0],[('B',entry),('H',),'nop',0]]
    return result

def check_wrapper(instructions,entry,halt,payload):
    forward,ticks,status = trace(instructions,entry,halt,payload)
    wrapped = clean(instructions,entry,halt)
    whole,clean_ticks,clean_status = trace(wrapped,('F',entry),('H',),payload,250)
    need((status == 'halt') == (clean_status == 'halt'), 'Halt equivalence in checked trace')
    if status == 'halt':
        expect = [(('F',q),n) for q,n in forward] + [(('B',q),n) for q,n in reversed(forward)] + [(('H',),payload)]
        need(whole == expect, 'Full logical forward/reverse/bridge trace')
        final = forward[-1][1]
        need(sum(clean_ticks) == 2*sum(ticks) + 192*(final+payload) + 16, 'Symmetric physical clock')
        need(whole[-1] == (('H',),payload), 'Entire raw payload and cofactor restored')
    else:
        need(all(q[0] == 'F' for q,n in whole), 'Stuck/cyclic forward copy never takes halt bridge')
    return status,forward,ticks

def gate_by_name(packet, prefix):
    matches = [row for row in packet['source'] if row[0].startswith(prefix) and row[0][len(prefix):].isdigit()]
    need(len(matches) == 1, 'Unique interface '+prefix)
    return matches[0]

def pack(packet, states, ticks, endpoint=None, requested_theta=None, requested_clean=None, height_doublings=0):
    """Build all outer positive candidates even for intentionally false endpoints."""
    mp = packet['mapping']
    K,m = mp['K'],mp['modulus']
    codes = mp['codes']
    path = [K*(N-1)+codes[q] for q,N in states]
    theta = sum(ticks) if requested_theta is None else requested_theta
    final = states[-1][1] if endpoint is None else endpoint
    target = K*(final-1)+mp['halt']
    start = path[0]
    qs,rs = zip(*(divmod(n-1,m) for n in path[:-1]))
    height = 1
    while height <= max([start+target+theta]+list(qs)):
        height *= 2
    need(type(height_doublings) is int and height_doublings >= 0, 'Nonnegative offline height choice')
    height *= 2**height_doublings
    radix_node = gate_by_name(packet,'radix_')
    multiplier = radix_node[2]
    B = multiplier*height*height
    P = B**len(ticks)
    J = (P-1)//(B-1)
    word = lambda values:sum(value*B**i for i,value in enumerate(values))
    W = word(qs)
    classes = sorted(set(a for a,d in mp['table']))[1:]
    E = [word([int(r==i) for r in rs]) for i in range(m)]
    Z = [word([q if mp['table'][r][0]==a else 0 for q,r in zip(qs,rs)]) for a in classes]
    actual_clock_word = word([mp['clocks'][r][0]*q + mp['clocks'][r][1] for q,r in zip(qs,rs)])
    # For deliberately incorrect theta, an arbitrary rounded quotient is used;
    # exact row checks below must reject it. Valid histories divide exactly.
    clock_quotient = 1+(actual_clock_word-theta)//(B-1)
    clean_time = packet['physical_clock_factor']*(2*theta+192*(states[0][1]+final)+16)
    values = dict(x=states[0][1]-1,Tclean=clean_time if requested_clean is None else requested_clean,
                  theta_positive=theta, final_positive=final, height_slack=height-start-target-theta,
                  global_slack=P-J-W-1-sum(Z)-len(Z), quotient_hat=W+1, clock_quotient_hat=clock_quotient)
    values.update({f'edge{i}_hat':v+1 for i,v in enumerate(E)})
    values.update({f'product{i}_hat':v+1 for i,v in enumerate(Z)})
    outer_rows = [row for row in packet['source'] if not row[0].startswith(('native__','clean_sos'))]
    env = execute(outer_rows,values)
    outer_pairs = [packet['comparisons'][i] for i in (0,1,18,19)]
    at = lambda x:env[x] if type(x) is str else x
    errors = [at(a)-at(b) for a,b in outer_pairs]
    names = {row[0]:row for row in packet['source']}
    H = env[names['native__scaled_A'][3]]
    M = env[names['native__scaled_B'][3]]
    A = env[names['native__scaled_Z'][3]]
    positive = all(values[n] > 0 for n in packet['auxiliaries'] if not n.startswith('native__'))
    return dict(values=values,errors=errors,positive=positive,joined_AND=(H & M)==A,height=height,radix=B,radix_multiplier=multiplier,scale=P,clock_word=actual_clock_word,encoded_path=path,steps=len(ticks),max_current_state=max(path[:-1]),tick_sum=sum(ticks),native_witnesses_materialized=False)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    counts=Counter()
    samples=[]
    rejection_samples=[]
    rng=random.Random(20261003)
    circuits=sorted((ROOT/'circuits').glob('*.json'))
    for path in circuits:
        packet=json.loads(path.read_text())
        if path.name.startswith('zero-step'):
            for x in range(65):
                right=packet['physical_clock_factor']*(384*(x+1)+16)
                for delta in (-1,0,1):
                    env=execute(packet['source'],dict(x=x,Tclean=right+delta))
                    need(env[packet['output']] == delta*delta,'Exact zero-step affine SOS')
                    counts['zero_step_exact_evaluations']+=1
            continue
        spec=packet['source_machine']
        mp=packet['mapping']
        state_by_code={code:name for name,code in mp['codes'].items()}
        need([n for n in packet['auxiliaries'] if n.startswith('edge')]==[f'edge{i}_hat' for i in range(mp['modulus'])], 'Every residue selector retained')
        for n in range(1,2401):
            value,code=divmod(n-1,mp['K']);value+=1;code+=1
            state=state_by_code.get(code)
            hit=instruction_step(spec['instructions'],'h',state,value)
            destination,following,tau=(mp['codes'][hit[0]],hit[1],hit[2]) if hit else (mp['trap'],value,192*value+8)
            q,r=divmod(n-1,mp['modulus']);a,d=mp['table'][r];c,b=mp['clocks'][r]
            need((a*q+d,c*q+b)==(mp['K']*(following-1)+destination,tau),'Literal residue totalization and clock')
            counts['residue_transition_clock_evaluations']+=1
        for N in range(1,97):
            status,states,ticks=check_wrapper(spec['instructions'],'s','h',N)
            counts['wrapper_halt_cases' if status=='halt' else 'wrapper_stuck_cases']+=1
            if status != 'halt':
                # Fake one-step arrival at halt must fail chronological transport.
                fake=pack(packet,[('s',N),('h',N)],[192*N+8])
                need(fake['errors'][1] != 0, 'Prime-three false halt rejected by retained endpoint/transport')
                counts['false_halt_transport_rejections']+=1
                if N == (3 if packet['fixture']=='zero3' else 1):
                    need(fake['positive'] and fake['joined_AND'] and fake['errors'][0]==fake['errors'][2]==fake['errors'][3]==0, 'False-halt counterexample isolates the chronological endpoint row')
                    rejection_samples.append(dict(fixture=path.stem,raw_payload=N,reason='False halt: genuine next control is rejecting trap, not halt',**fake))
                continue
            packed=pack(packet,states,ticks)
            need(packed['positive'] and packed['errors']==[0]*4 and packed['joined_AND'],'Complete outer packed checks')
            h,B=packed['height'],packed['radix']
            need(packed['steps'] <= mp['modulus']*h and packed['max_current_state'] <= mp['modulus']*h,'Distinct-state duration bound')
            need(all(0<t<=2384*h for t in ticks) and sum(ticks)<=2384*mp['modulus']*h*h<B-1,'Strict no-wrap upper bound')
            need(0<sum(ticks)<h<B-1,'Positive requested time and height')
            need(packed['clock_word'] == (B-1)*(packed['values']['clock_quotient_hat']-1)+sum(ticks),'Exact paid congruence')
            need((sum(ticks)+(B-1))>=h,'Wrapped requested time cannot fit positive height slack')
            expected=(1584*N+48 if packet['fixture']=='incdec' else 768*N+32)*packet['physical_clock_factor']
            need(packed['values']['Tclean']==expected,'Fixture closed-form clean clock')
            counts['accepted_full_outer_histories']+=1
            counts['strict_no_wrap_checks']+=1
            if N in (1,3,5):
                eta_values={packed['values']['height_slack']}
                for j in (1,2,3):
                    extension=pack(packet,states,ticks,height_doublings=j)
                    need(extension['positive'] and extension['joined_AND'] and extension['errors']==[0]*4,'Every checked larger dyadic height extends the same accepted relation')
                    need(extension['values']['Tclean']==packed['values']['Tclean'],'Height variation preserves free input and clean time')
                    eta_values.add(extension['values']['height_slack'])
                    counts['larger_height_outer_extensions']+=1
                need(len(eta_values)==4,'Retained height slacks distinguish witness candidates')
            wrong=pack(packet,states,ticks,requested_clean=expected+1)
            need(wrong['errors'][:3]==[0,0,0] and wrong['errors'][3]==-1,'One-tick clean mutation')
            counts['clean_time_mutation_rejections']+=1
            wrong=pack(packet,states,ticks,requested_theta=sum(ticks)-1)
            need(wrong['positive'] and wrong['errors'][2] != 0,'Positive native time mutation')
            counts['native_time_mutation_rejections']+=1
            wrong=pack(packet,states,ticks,endpoint=states[-1][1]+1)
            need(wrong['errors'][1] != 0,'Wrong terminal payload')
            counts['terminal_payload_mutation_rejections']+=1
            if N in (1,3,5,7,12,96):
                samples.append(dict(fixture=path.stem,**packed))
        # Coprime scaling preserves controls and scales tau-8.
        for N in range(1,25):
            for multiplier in (5,7,11):
                a,ta,sa=trace(spec['instructions'],'s','h',N)
                b,tb,sb=trace(spec['instructions'],'s','h',multiplier*N)
                need(sa==sb and [q for q,n in a]==[q for q,n in b] and [multiplier*n for q,n in a]==[n for q,n in b],'Raw valuation/cofactor invariance')
                need([multiplier*(v-8)+8 for v in ta]==tb,'Cofactor physical clock scaling')
                counts['coprime_scaled_trace_cases']+=1
        # Execute every native gate without claiming these signed values are zeros.
        for i in range(48):
            vals={n:rng.randrange(-8,9) for n in packet['parameters']+packet['auxiliaries']}
            modulus=(1000003,1000033,2147483647)[i%3]
            env=execute(packet['source'],vals,modulus)
            rs=residuals(packet,env)
            need(env[packet['output']] == sum(v*v for v in rs)%modulus,'Complete modular SOS including all native rows')
            counts['full_signed_modular_SOS_evaluations']+=1
    # Distinct final payload, genuine arithmetic divisions, every primitive,
    # zero-step, delayed stuck, and a nonhalting fresh-entry cycle.
    extra=[('inc2',[['s','h','inc',0]],'s','h',[1,5,7]),
           ('inc3',[['s','h','inc',1]],'s','h',[1,5,7]),
           ('dec2',[['s','h','dec',0]],'s','h',[2,10,14,3]),
           ('dec3',[['s','h','dec',1]],'s','h',[3,15,21,2]),
           ('zero2',[['s','h','zero',0]],'s','h',[1,5,2]),
           ('positive2',[['s','h','positive',0]],'s','h',[2,10,1]),
           ('initial_halt',[],'h','h',[1,5,7]),
           ('delayed_stuck',[['s','a','nop',0],['a','h','dec',1]],'s','h',[1,5,6]),
           ('growing_nonhalt',[['s','a','zero',0],['a','b','inc',0],['b','a','positive',0]],'s','h',[1,5,2])]
    for name,instructions,entry,halt,payloads in extra:
        for N in payloads:
            status,states,ticks=check_wrapper(instructions,entry,halt,N)
            counts['additional_wrapper_checks']+=1
            if status=='halt' and states[-1][1] != N:
                counts['distinct_final_payload_checks']+=1
    try:
        clean([['s','a','zero',0],['a','s','inc',0],['s','h','positive',0]],'s','h')
    except ValueError:
        counts['nonfresh_entry_rejections']+=1
    else:
        raise ValueError('Returning entry must be rejected')
    receipt=dict(format='clean-clock-semantic-checks-v1',status='PASS',counts=dict(counts),outer_samples=samples,false_halt_regressions=rejection_samples,native_positive_Pell_witnesses_materialized=False,third_party_executable_code_run=False,limits='Finite checks supplement inherited native and CA theorems and the new composition proof. No runtime bound or universality follows from samples.')
    dest=ROOT/'receipts/semantics.json'
    content=json.dumps(receipt,indent=2,sort_keys=True)+'\n'
    if args.check:
        need(dest.read_text()==content,'Exact deterministic semantic replay')
    else:
        dest.write_text(content)
    print(json.dumps(dict(status='PASS',counts=dict(counts)),sort_keys=True))

if __name__=='__main__':
    main()

#!/usr/bin/env python3
"""Actual native and radius-one lattice replay plus independent certificate checks."""
from copy import deepcopy
from itertools import product
from pathlib import Path
import gc
import hashlib
import json
import sys
import time
import clean_targets as ct
from check_clean_targets import check
from vendor.three_mass_collision_generator import ThreeMassCA, Instruction as CAInstruction
from vendor.spatial_radius_one import SpatialRadiusOneCA
from vendor.radius_one import RadiusOneCA

ROOT = Path(__file__).resolve().parent
I, M = ct.Instruction, ct.Machine


def require(ok, message='test assertion failed'):
    if not ok: raise AssertionError(message)


def rejects(f):
    try: f()
    except (ValueError, KeyError, TypeError): return
    raise AssertionError('expected rejection')


def source_step(machine, q, n):
    enabled = []
    for i in machine.instructions:
        if i.source != q: continue
        p = 2+i.counter
        if i.operation in ('positive', 'dec') and n % p: continue
        if i.operation == 'zero' and n % p == 0: continue
        enabled.append(i)
    require(len(enabled) <= 1)
    if not enabled: return None
    i = enabled[0]; p = 2+i.counter
    return i.target, n*p if i.operation == 'inc' else n//p if i.operation == 'dec' else n


def count_formula(q, m, d):
    return {'types': 96*q*m+6*q*d+2*d+6*q+2314,
            'prescribed_pairs': 3528*q*m+6*q*d+d-6*m+1152,
            'completed_pairs': 7008*q*m+12*q*d+2*d+6*q-6*m+2304}


def make_ca(machine):
    return ThreeMassCA(machine.states, machine.halt,
        [CAInstruction(i.source, i.target, i.operation, i.counter) for i in machine.instructions])


def replay(ca, cert, witness, wrappers=False):
    result = check(cert, witness)
    wrapped, initial = ct.clean_source(ct.core.machine_from_json(cert['forward_certificate']['machine']),
                                      cert['forward_certificate']['initial_state'])
    trace = result['cleaned_source_trace']
    require(cert['model'] == 'native')
    n0 = trace[0]['N']; current = ca.initial(initial, n0); target = ca.initial('H', n0)
    canonical = {row['microtime']: (row['state'], row['N']) for row in trace}
    require(ca.ready(current) == canonical[0]); require(current != target)
    spatial, phase = (SpatialRadiusOneCA(ca), RadiusOneCA(ca, 4)) if wrappers else (None, None)
    if wrappers:
        packed, phased = spatial.embed(current), phase.embed(current)
        packed_target, phase_target = spatial.embed(target), phase.embed(target)
        require(min(x for x,t in packed_target) == -3*n0)
    physical = result['physical_time']
    for tick in range(1, physical+1):
        previous = current
        current = ca.step(current, require_specified=True)
        require(len(current) == 3 and len(set(current)) == 3)
        require(ca.ready(current) == canonical.get(tick), ('boundary', tick, ca.ready(current), canonical.get(tick)))
        require((current == target) == (tick == physical), 'early or missing exact target')
        if wrappers:
            old_packed = packed; packed = spatial.step(packed)
            require(spatial.inverse_step(packed) == old_packed)
            require(packed == spatial.embed(current))
            require((packed == packed_target) == (tick == physical))
            for micro in range(4):
                old_phased = phased; phased = phase.step(phased)
                require(phase.inverse_step(phased) == old_phased)
                require(len(phased) == 3)
                require((phased == phase_target) == (tick == physical and micro == 3))
            require(phase.project(phased) == current)
    # Independently execute every decoded source edge, including both switches.
    for before, after in zip(trace, trace[1:]):
        require(source_step(wrapped, before['state'], before['N']) == (after['state'], after['N']))
    require(current == target)
    return {'N': n0, 'original_source_horizon': cert['forward_certificate']['horizon'],
            'cleaned_source_horizon': len(trace)-1, 'physical_time': physical,
            'all_three_models': wrappers, 'final_N': trace[-1]['N']}


def stalled_replay(ca, initial, n):
    current = ca.initial(initial, n); target = ca.initial('H', n); ticks = 0
    while not any(ca.names[t][0] == 'trap' for x,t in current):
        current = ca.step(current, require_specified=True); ticks += 1
        require(current != target and ticks <= 10000*n+1000)
    at_trap = ticks
    right_marker = next(x for x,t in current if ca.names[t][0] == 'R')
    trap = next(x for x,t in current if ca.names[t][0] == 'trap')
    escape = next(x for x,t in current if ca.names[t][0] == 'escape')
    require(escape < trap < right_marker)
    for j in range(37):
        current = ca.step(current, require_specified=True); ticks += 1
        require(current != target and len(current) == 3 and ca.ready(current) is None)
        require(next(x for x,t in current if ca.names[t][0] == 'escape') == escape-j-1)
    return {'N': n, 'trap_time': at_trap, 'ticks_checked': ticks}


def main():
    start = time.monotonic(); cases=[]; stalls=[]; counts=[]; exhaustive=0; mutations=0
    programs=[]
    for op, counter in [('inc',0),('inc',1),('dec',0),('dec',1),('zero',0),('zero',1),('positive',0),('positive',1),('nop',0)]:
        programs.append((op+str(counter), M(('s','h'),'h',(I('s','h',op,counter),)), 's', 1, range(1,7)))
    programs.append(('delayed_stall', M(('s','a','h'),'h',(I('s','a','nop'),I('a','h','dec',0))), 's', 2, [1,2,3]))
    programs.append(('h0', M(('h',),'h',()), 'h', 0, [1,5]))
    programs.append(('branch_merge3', M(('s','a','b','h'),'h',
                     (I('s','a','zero',1),I('s','b','positive',1),I('a','h','zero',1),I('b','h','positive',1))), 's',2,[1,2,3,5,6]))
    chain_ops=[('inc',0),('inc',1),('dec',0),('dec',1),('inc',0)]
    chain=M(tuple('q'+str(j) for j in range(6)), 'q5',
            tuple(I('q'+str(j),'q'+str(j+1),op,c) for j,(op,c) in enumerate(chain_ops)))
    programs.append(('chain_all_arithmetic',chain,'q0',5,[1,5]))
    for label,machine,initial,horizon,inputs in programs:
        wrapped, initial_clean = ct.clean_source(machine, initial)
        old, new = ct.source_ledger(machine), ct.source_ledger(wrapped)
        require(new['states']==2*old['states']+1 and new['instructions']==2*old['instructions']+2)
        require(new['instruction_modulus']==2*old['instruction_modulus']+1)
        require(new['arithmetic_instructions']==2*old['arithmetic_instructions'])
        require(new['expanded_branches']==2*old['expanded_branches']+2)
        ca=make_ca(wrapped)
        expected=count_formula(new['states'],new['instruction_modulus'],new['arithmetic_instructions'])
        observed={'types':len(ca.names),'prescribed_pairs':ca.required_pair_count,'completed_pairs':len(ca.pairs)}
        require(observed==expected)
        counts.append({'label':label,'old_source':old,'cleaned_source':new,'actual_ca':observed})
        for n in inputs:
            cert=ct.export_clean_certificate(machine,initial,horizon,{'mode':'fixed_raw','N':n}, {'mode':'free'})
            q_test,n_test=initial,n
            for _ in range(horizon):
                edge=source_step(machine,q_test,n_test)
                if edge is None: break
                q_test,n_test=edge
            enabled=q_test==machine.halt
            if not enabled:
                rejects(lambda:ct.make_clean_witness(cert)); stalls.append({'program':label,**stalled_replay(ca,initial_clean,n)})
                continue
            witness=ct.make_clean_witness(cert)
            # Wrapper replay for every op and both zero-3 residues, plus a full chain and h=0.
            all_models=n in ([1,2] if label=='zero1' else [1] if label not in ('dec0','dec1','positive0','positive1') else [2+machine.instructions[0].counter])
            cases.append({'program':label,**replay(ca,cert,witness,all_models)})
            if len(machine.branches())==1 and horizon==1 and n<=3:
                simple=ct.export_clean_certificate(machine,initial,1,{'mode':'fixed_raw','N':n})
                zeros=[]
                for e,u in product(range(4),range(5)):
                    w={'e_0_0':e,'u_0_0':u}
                    if ct.core.polynomial_value(simple,w)==0:zeros.append(w)
                    exhaustive+=1
                require(zeros==[ct.make_clean_witness(simple)])
            # Same witness verifies the phase clock and spatial clock with no extra source variables.
            for model in ('spatial-radius-one','phase-radius-one'):
                c=ct.export_clean_certificate(machine,initial,horizon,{'mode':'fixed_raw','N':n},{'mode':'free'},model)
                w=ct.make_clean_witness(c); r=check(c,w)
                require(r['physical_time']==check(cert,witness)['physical_time']*(4 if model=='phase-radius-one' else 1))
            fixed=ct.export_clean_certificate(machine,initial,horizon,{'mode':'fixed_raw','N':n},
                                             {'mode':'fixed','value':check(cert,witness)['physical_time']})
            check(fixed,ct.make_clean_witness(fixed))
            wrong=deepcopy(fixed); wrong['time_spec']['value']+=1
            rejects(lambda:check(wrong,ct.make_clean_witness(fixed)));mutations+=1
        del ca;gc.collect()
    # Unbounded source run from a fresh start: value doubles once per two instructions.
    growing=M(('s','a','b','h'),'h',(I('s','a','zero',0),I('a','b','inc',0),I('b','a','positive',0)))
    wm,wi=ct.clean_source(growing,'s');ca=make_ca(wm); current=ca.initial(wi,1)
    seen=[]; ticks=0
    while len(seen)<9:
        current=ca.step(current,require_specified=True);ticks+=1
        require(current!=ca.initial('H',1))
        r=ca.ready(current)
        if r: seen.append(r)
        require(ticks<100000)
    require(seen==[('F:a',1),('F:b',2),('F:a',2),('F:b',4),('F:a',4),('F:b',8),('F:a',8),('F:b',16),('F:a',16)])
    growth={'ticks_checked':ticks,'committed_sections':seen}
    del ca;gc.collect()
    for h in range(10): rejects(lambda h=h:ct.make_clean_witness(ct.export_clean_certificate(growing,'s',h,{'mode':'fixed_raw','N':1})))
    # Freshness must be checked structurally even if the incoming instruction's guard is disabled on this input.
    incoming=M(('s','p','h'),'h',(I('p','s','positive',0),I('s','h','nop')))
    rejects(lambda:ct.clean_source(incoming,'s'))
    loop=M(('s','h'),'h',(I('s','s','inc'),))
    rejects(lambda:ct.clean_source(loop,'s'))
    badhalt=M(('s','h'),'h',(I('s','h','nop'),I('h','s','nop')))
    rejects(lambda:ct.clean_source(badhalt,'s'))
    # An actual return to the old initial state breaks naive cleanup, not merely syntax.
    returning=M(('s','a','h'),'h',(I('s','a','zero',0),I('a','s','inc',0),I('s','h','positive',0))).validate()
    rejects(lambda:ct.clean_source(returning,'s'))
    q,n='s',1; returned=[(q,n)]
    for _ in range(3):
        q,n=source_step(returning,q,n);returned.append((q,n))
    require(returned==[('s',1),('a',1),('s',2),('h',2)])
    # Its first backward state B:s is at N=2; an unguarded exit would restore the wrong input.
    premature_exit_N=returned[-2][1];require(premature_exit_N==2 and premature_exit_N!=returned[0][1])
    # Free raw input and paid bounded loader preserve fiberwise uniqueness.
    simple=M(('s','h'),'h',(I('s','h','inc',0),))
    for mode,free in [({'mode':'free_raw','name':'x'},{'x':4}),
                      ({'mode':'bounded_counters','A':2,'B':2},{'input_a':1,'input_b':2})]:
        c=ct.export_clean_certificate(simple,'s',1,mode,{'mode':'free'}); w=ct.make_clean_witness(c,free);r=check(c,w)
        require(r['exact_target_N']==(5 if 'x' in free else 18))
    c=ct.export_clean_certificate(chain,'q0',5,{'mode':'fixed_raw','N':5},{'mode':'free'})
    c['expanded_polynomial']=ct.core.expand_polynomial(c);w=ct.make_clean_witness(c);r=check(c,w)
    mods=[]
    for key,value in [('exact_target_state','F:q5'),('exact_target_N',{'':10}),('clock_scale',4),('cleaned_source_horizon',11),('physical_time',{'':1})]:
        d=deepcopy(c);d[key]=value;mods.append(d)
    d=deepcopy(c);d['cleaned_machine']['instructions'][5]['operation']='inc';mods.append(d)
    d=deepcopy(c);d['ledger']['core_variables']*=2;mods.append(d)
    d=deepcopy(c);d['squares'][-1]['affine']['']=d['squares'][-1]['affine'].get('',0)+1;mods.append(d)
    d=deepcopy(c);d['expanded_polynomial'][0]['coefficient']+=1;mods.append(d)
    for d in mods:rejects(lambda d=d:check(d,w));mutations+=1
    for key in list(w)[:8]:
        v=dict(w);v[key]+=1;rejects(lambda v=v:check(c,v));mutations+=1
    v=dict(w);v[next(iter(v))]=True;rejects(lambda:check(c,v));mutations+=1
    # Every selected instruction clock is exactly symmetric with its reversed source instruction.
    symmetry=0
    for op,counter in [('inc',0),('inc',1),('dec',0),('dec',1),('zero',0),('zero',1),('positive',0),('positive',1),('nop',0)]:
        p=2+counter
        for n in range(1,25):
            if op in ('dec','positive') and n%p:continue
            if op=='zero' and n%p==0:continue
            n1=n*p if op=='inc' else n//p if op=='dec' else n
            t=108*n+96*n1+8 if op=='inc' else 96*n+108*n1+8 if op=='dec' else 192*n+8
            reverse='dec' if op=='inc' else 'inc' if op=='dec' else op
            rt=108*n1+96*n+8 if reverse=='inc' else 96*n1+108*n+8 if reverse=='dec' else 192*n1+8
            require(t==rt);symmetry+=1
    for name,obj in [('chain_certificate',c),('chain_witness',w),('chain_receipt',r)]:
        (ROOT/'examples'/(name+'.json')).write_text(json.dumps(obj,indent=2)+'\n')
    request={'machine':ct.machine_json(chain),'initial_state':'q0','horizon':5,
             'input_spec':{'mode':'fixed_raw','N':5},'time_spec':{'mode':'free'}}
    (ROOT/'examples'/'chain_request.json').write_text(json.dumps(request,indent=2)+'\n')
    receipt={'status':'passed','lattice_replays':cases,'stalled_replays':stalls,'source_and_ca_counts':counts,
             'growing_nonhalt_prefix':growth,'fresh_start_counterexample':{'forward_trace':returned,'naive_exit_N':premature_exit_N},'exhaustive_natural_assignments':exhaustive,
             'rejected_mutations':mutations,'clock_symmetry_cases':symmetry,
             'native_ticks_replayed':sum(c['physical_time'] for c in cases)+sum(s['ticks_checked'] for s in stalls)+ticks,
             'spatial_ticks_replayed':sum(c['physical_time'] for c in cases if c['all_three_models']),
             'phase_ticks_replayed':sum(4*c['physical_time'] for c in cases if c['all_three_models']),
             'elapsed_seconds':round(time.monotonic()-start,3),
             'vendor_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((ROOT/'vendor').glob('*.py'))}}
    (ROOT/'receipts'/'test_clean_targets.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k not in ('lattice_replays','stalled_replays','source_and_ca_counts','vendor_sha256')},indent=2))

if __name__=='__main__':main()

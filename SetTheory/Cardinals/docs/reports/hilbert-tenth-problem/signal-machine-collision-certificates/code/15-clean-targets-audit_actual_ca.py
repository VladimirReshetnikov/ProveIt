#!/usr/bin/env python3
"""Independent cleanup audit. Writes only the receipt selected by the caller.
The source wrapper and source interpreter below do not import clean_targets.py.
The CA's generated singleton/pair maps are stepped by a separate local updater.
"""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import importlib.util
from collections import defaultdict
from dataclasses import dataclass
import gc, hashlib, json

HERE = Path(__file__).resolve().parent
RELEASE = HERE.parent
CLEAN = HERE.parent

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod

ca_mod = load('audit_generator', RELEASE/'vendor/three_mass_collision_generator.py')
sp_mod = load('audit_spatial', RELEASE/'vendor/spatial_radius_one.py')
ph_mod = load('audit_phase', RELEASE/'vendor/radius_one.py')
core = load('audit_certificate', RELEASE/'vendor/certificate.py')
I = core.Instruction

def wrapped(states, halt, instructions, initial):
    core.Machine(states, halt, instructions).validate()
    if initial not in states or any(i.target == initial for i in instructions):
        raise ValueError('initial not fresh')
    inv = {'inc':'dec','dec':'inc','zero':'zero','positive':'positive','nop':'nop'}
    out = [I('F:'+i.source,'F:'+i.target,i.operation,i.counter) for i in instructions]
    out += [I('B:'+i.target,'B:'+i.source,inv[i.operation],i.counter) for i in instructions]
    out += [I('F:'+halt,'B:'+halt,'nop'),I('B:'+initial,'H','nop')]
    m = core.Machine(tuple('F:'+q for q in states)+tuple('B:'+q for q in states)+('H',),'H',tuple(out)).validate()
    return m

def execute(machine, q, N, limit):
    trace=[(q,N,0)]
    for _ in range(limit):
        if q == machine.halt: return trace, 'halt'
        valid=[]
        for ins in machine.instructions:
            if ins.source != q: continue
            p=(2,3)[ins.counter]
            if ins.operation in ('dec','positive') and N%p: continue
            if ins.operation=='zero' and N%p==0: continue
            valid.append(ins)
        assert len(valid)<=1
        if not valid:return trace,'stuck'
        ins=valid[0]; before=N; p=(2,3)[ins.counter]
        if ins.operation=='inc':N*=p
        if ins.operation=='dec':N//=p
        # Derive independently from four queries + three gates + arithmetic.
        arith = 12*min(before,N)+1 if ins.operation in ('inc','dec') else 1
        dt=2*(48*before+1)+2*(48*N+1)+3+arith
        q=ins.target;trace.append((q,N,trace[-1][2]+dt))
    return trace, 'halt' if q==machine.halt else 'running'

def tick(ca, conf, required):
    cells=defaultdict(list)
    for pos,t in conf:cells[pos].append(t)
    out=[]
    for pos,types in cells.items():
        p=tuple(sorted(types));assert len(set(p))==len(p)
        if len(p)==1:o=(ca.single[p[0]],)
        elif len(p)==2:
            if required:assert p in ca.specified_pairs, ('unspecified pair',p)
            o=ca.pairs.get(p,p)
        else:
            assert not required,('triple collision',p)
            o=p
        out.extend((pos+ca.velocity[t],t) for t in o)
    assert len(out)==3 and len(set(out))==3
    return tuple(sorted(out))

def inverse_tick(ca, conf):
    si={b:a for a,b in ca.single.items()}
    cells=defaultdict(list)
    for x,t in conf:cells[x-ca.velocity[t]].append(t)
    out=[]
    for x,ts in cells.items():
        p=tuple(sorted(ts))
        o=(si[p[0]],) if len(p)==1 else ca.pair_preimage.get(p,p) if len(p)==2 else p
        out.extend((x,t) for t in o)
    return tuple(sorted(out))

def canonical(ca,q,N):
    return tuple(sorted(((-12*N,ca.type_ids[('L',0,(q,0,0))]),
                         (-12*N,ca.type_ids[('S',0)]),(0,ca.R))))

def observe(ca,conf):
    # This is exact full-configuration matching, not the compiler ready helper.
    for x,t in conf:
        name=ca.names[t]
        if name[:2]==('L',0) and name[2][1:]==(0,0) and x<0 and x%12==0:
            q=name[2][0];N=-x//12
            if conf==canonical(ca,q,N):return q,N
    return None

def size_formula(q,m,d):
    return {'types':96*q*m+6*q*d+2*d+6*q+2314,
            'required_pairs':3528*q*m+6*q*d+d-6*m+1152,
            'completed_pairs':7008*q*m+12*q*d+2*d+6*q-6*m+2304}

def check_case(label,states,halt,ins,initial,inputs,wrappers=False):
    machine=core.Machine(states,halt,tuple(ins)).validate()
    cm=wrapped(states,halt,ins,initial)
    q,J,d,B=len(states),len(ins),sum(i.operation in ('inc','dec') for i in ins),len(machine.branches())
    assert (len(cm.states),len(cm.instructions),len(cm.instructions)+1,
            sum(i.operation in ('inc','dec') for i in cm.instructions),len(cm.branches())) == (2*q+1,2*J+2,2*(J+1)+1,2*d,2*B+2)
    ca=ca_mod.ThreeMassCA(cm.states,'H',[ca_mod.Instruction(i.source,i.target,i.operation,i.counter) for i in cm.instructions])
    observed_size={'types':len(ca.names),'required_pairs':ca.required_pair_count,'completed_pairs':len(ca.pairs)}
    assert observed_size==size_formula(2*q+1,2*J+3,2*d)
    results=[]
    for N in inputs:
        forward,status=execute(machine,initial,N,20)
        ctl,cstatus=execute(cm,'F:'+initial,N,42)
        conf=canonical(ca,'F:'+initial,N); target=canonical(ca,'H',N)
        seen=[('F:'+initial,N,0)]
        if status=='halt':
            h=len(forward)-1;theta=forward[-1][2];Nh=forward[-1][1]
            expectedT=2*theta+192*(Nh+N)+16
            assert cstatus=='halt' and len(ctl)==2*h+3 and ctl[-1]==('H',N,expectedT)
            expected_states=[('F:'+q,n) for q,n,t in forward]+[('B:'+q,n) for q,n,t in reversed(forward)]+[('H',N)]
            assert [(q,n) for q,n,t in ctl]==expected_states
            sp=sp_mod.SpatialRadiusOneCA(ca,4) if wrappers else None
            ph=ph_mod.RadiusOneCA(ca,4) if wrappers else None
            scon=sp.embed(conf) if sp else None;pcon=ph.embed(conf) if ph else None
            starget=sp.embed(target) if sp else None;ptarget=ph.embed(target) if ph else None
            for t in range(1,expectedT+1):
                old=conf;conf=tick(ca,conf,True)
                # Global inverse checked at every canonical boundary and final tick.
                ready=observe(ca,conf)
                if ready:
                    assert inverse_tick(ca,conf)==old
                    seen.append((*ready,t))
                assert (conf==target)==(t==expectedT)
                if sp:
                    scon=sp.step(scon)
                    assert scon==sp.embed(conf)
                    assert (scon==starget)==(t==expectedT)
                    for phase in range(1,5):
                        pcon=ph.step(pcon)
                        assert (pcon==ptarget)==(t==expectedT and phase==4)
                    assert pcon==ph.embed(conf)
            assert seen==ctl,(label,N,seen,ctl)
            # Halt is an event; verify the completed update does not freeze it.
            after=tick(ca,conf,False)
            assert after!=conf and inverse_tick(ca,after)==conf
            results.append({'N0':N,'Nh':Nh,'h':h,'forward_ticks':theta,'first_exact_target_tick':expectedT,
                            'canonical_trace':seen,'spatial_same_clock':bool(sp),'phase_times_four':bool(ph)})
        else:
            assert status=='stuck'
            # Continue well past finite dispatch to escape, never touching completion.
            end=ctl[-1][2]+96*ctl[-1][1]+8+200
            for t in range(1,end+1):
                conf=tick(ca,conf,True)
                assert conf!=target
                assert not any(ca.names[k][0]=='L' and ca.names[k][2][0]=='H' for _,k in conf)
            assert any(ca.names[k][0]=='escape' for _,k in conf)
            results.append({'N0':N,'source_status':'stuck','specified_ticks_tested':end,'escaping':True})
    del ca;gc.collect()
    return {'case':label,'sizes':observed_size,'runs':results}

def main():
    outputs=[]
    outputs.append(check_case('already_halted',('q0',),'q0',[],'q0',[1,5],True))
    for op in ('inc','dec','nop','zero','positive'):
        for k,p in enumerate((2,3)):
            inputs=[1,5] if op in ('inc','nop') else [p,5*p,1] if op in ('dec','positive') else [1,5,p]
            outputs.append(check_case(op+str(p),('q0','qh'),'qh',[I('q0','qh',op,k)],'q0',inputs,
                                      wrappers=(op=='inc' and k==0)))
    outputs.append(check_case('two_step_inc3_dec2',('q0','q1','qh'),'qh',
                             [I('q0','q1','inc',1),I('q1','qh','dec',0)],'q0',[2,10]))
    outputs.append(check_case('incoming_test_merge',('q0','other','qh'),'qh',
                             [I('q0','qh','zero',1),I('other','qh','positive',1)],'q0',[1,5,3]))
    outputs.append(check_case('missing_instruction',('q0','qh'),'qh',[],'q0',[1,5]))
    # Required freshness counterexample is a valid separated reversible source,
    # but its inverse at B:q0 already has a DEC, conflicting with a naive exit.
    bad=core.Machine(('q0','q1','qh'),'qh',(
        I('q0','q1','zero',0),I('q1','q0','inc',0),I('q0','qh','positive',0))).validate()
    try:wrapped(bad.states,bad.halt,bad.instructions,'q0')
    except ValueError:pass
    else:raise AssertionError('nonfresh source accepted')
    bt,bs=execute(bad,'q0',1,10)
    assert bs=='halt' and [(q,n) for q,n,t in bt]==[('q0',1),('q1',1),('q0',2),('qh',2)]
    return {'status':'PASS','method':'Independent wrapper, source interpreter, CA collision/stream updater, full exact-target comparisons',
            'cases':outputs,'freshness_counterexample_rejected':True,
            'release_hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [RELEASE/'vendor/three_mass_collision_generator.py',RELEASE/'vendor/certificate.py']}}

if __name__=='__main__':
    result=main()
    (HERE/'actual-ca-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'cases':len(result['cases']),
                      'runs':sum(len(c['runs']) for c in result['cases']),
                      'receipt':'actual-ca-receipt.json'},indent=2))

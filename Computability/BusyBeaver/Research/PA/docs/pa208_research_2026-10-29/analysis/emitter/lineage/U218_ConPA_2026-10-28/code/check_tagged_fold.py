#!/usr/bin/env python3
"""Independent finite local proof of the left-tag 219 -> 218 state fold.

The source/compiler/runtime are not imported.  Exhaustive finite local frames
verify the old invariant and every 1/3/5-step stuttering simulation block.
Unrepresented exterior cells are opaque: the checker refuses to read them.
"""
from pathlib import Path
import argparse, hashlib, itertools, json


def require(condition, reason):
    if not condition:raise ValueError(reason)


def read(path):
    table={};starts=[]
    for line in path.read_text().splitlines():
        if line.startswith('#! start'):
            require(line=='#! start 0','initial header must be exactly #! start 0')
            starts.append(0);continue
        if not line.strip() or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        require(q>=0 and z>=0 and b in (0,1) and w in (0,1) and d in ('L','R'),'invalid row')
        require((q,b) not in table,'duplicate row')
        table[q,b]=(w,1 if d=='R' else -1,z)
    require(starts==[0],'exactly one start header required')
    states={q for q,b in table}
    require(0 in states,'start missing')
    require(set(table)=={(q,b) for q in states for b in (0,1)},'incomplete binary table')
    require({z for w,d,z in table.values()}-states=={254},'incorrect halt label')
    return table,states


def rename(q):return 182 if q==507 else q


def invariant(q,h,tape):
    return (q!=182 or tape[h-1]==1) and (q!=507 or tape[h-1]==0)


def local_certificate(old,new,states,predicate=invariant):
    admitted=0;lengths={1:0,3:0,5:0};examples={}
    for q in sorted(states):
        for bits in itertools.product((0,1),repeat=5):
            tape=dict(zip(range(-2,3),bits))
            if not predicate(q,0,tape):continue
            admitted+=1
            b=tape[0];w,d,z=old[q,b]
            wanted=dict(tape);wanted[0]=w
            require(predicate(z,d,wanted),('old tag invariant not inductive',q,bits))
            ticks=3 if (q,b)==(182,0) else 5 if (q,b)==(507,0) else 1
            nq,nh,nt=rename(q),0,dict(tape);trace=[]
            for k in range(ticks):
                require(nq!=254,('premature halt in simulation block',q,bits,k))
                require(nh in nt,('opaque exterior read',q,bits,nh))
                nb=nt[nh];nw,nd,nz=new[nq,nb]
                trace.append([nq,nh,nb,nw,nd,nz])
                nt[nh]=nw;nh+=nd;nq=nz
                if k+1<ticks:require(nq!=254,('intermediate halt',q,bits,k))
            require((nq,nh,nt)==(rename(z),d,wanted),('local simulation mismatch',q,bits,trace))
            lengths[ticks]+=1
            if q in (182,507) and f'{q}/{b}' not in examples:
                examples[f'{q}/{b}']={'old_action':[w,d,z],
                                     'left_tag':tape[-1],'new_steps':ticks,'trace':trace}
    return admitted,lengths,examples


def check(old_path,new_path):
    old,states=read(old_path);new,new_states=read(new_path)
    require(len(states)==219 and len(new_states)==218,'wrong working-state counts')
    require(new_states==states-{507},'wrong deleted state')
    pred=lambda q:sorted([[s,b,w,d,z] for (s,b),(w,d,z) in old.items() if z==q])
    require(pred(182)==[[173,1,1,1,182]],'unexpected original-state predecessor')
    require(pred(507)==[[18,0,0,1,507],[134,0,0,1,507],[188,0,0,1,507]],'unexpected clone predecessor')
    require(old[182,0]==(0,1,76) and old[507,0]==(0,1,90),'unexpected differentiated actions')
    require(old[182,1]==old[507,1]==(1,1,61),'unexpected common action')
    expected={(q,b):(w,d,rename(z)) for (q,b),(w,d,z) in old.items() if q!=507}
    expected[182,0]=(0,-1,209)
    require(new==expected,'candidate differs from exact tag-dispatch transformation')
    admitted,lengths,examples=local_certificate(old,new,states)
    return {'status':'EXHAUSTIVE_LOCAL_TAG_INVARIANT_AND_STUTTER_SIMULATION_PASS',
        'old_sha256':hashlib.sha256(old_path.read_bytes()).hexdigest(),
        'new_sha256':hashlib.sha256(new_path.read_bytes()).hexdigest(),
        'old_working_states':len(states),'new_working_states':len(new_states),
        'initial_state':0,'halt_label':254,'initial_tapes':'ALL_BINARY_TAPES',
        'old_invariant':['q=182 implies tape[head-1]=1','q=507 implies tape[head-1]=0'],
        'old_predecessors':{'182':pred(182),'507':pred(507)},
        'state_map':{'507':182,'all_other_states':'identity'},
        'all_radius_two_frames':len(states)*32,'admissible_frames':admitted,
        'simulation_lengths':lengths,'special_blocks':examples,
        'changed_retained_rows':[[q,b,*old[q,b],*act] for (q,b),act in sorted(new.items()) if old[q,b]!=act],
        'deleted_rows':[[507,b,*old[507,b]] for b in (0,1)],
        'time_reindexing':'tau(0)=0; tau(n+1)-tau(n) is 1, 3, or 5; n <= tau(n) <= 5n',
        'forward_halting_bound':'Old halt at n implies new halt at tau(n) <= 5n.',
        'reverse_halting_bound':'New halt at m implies old halt at some n <= m, since all intermediate simulation states are nonhalting.',
        'preservation':'At each paired boundary, identical tape and head and mapped control state. No intermediate halts. The unknown exterior is neither read nor changed in each checked block.',
        'scope':'Source-independent finite local invariant and bounded stuttering simulation, yielding PA-provable blank halting equivalence by induction. This does not prove the source-theory endpoint by itself.',
        'kernel_certificate':False}

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('old',type=Path);ap.add_argument('new',type=Path);ap.add_argument('--output',type=Path)
    a=ap.parse_args();r=check(a.old,a.new);s=json.dumps(r,indent=2)+'\n'
    if a.output:a.output.write_text(s)
    print(s,end='')

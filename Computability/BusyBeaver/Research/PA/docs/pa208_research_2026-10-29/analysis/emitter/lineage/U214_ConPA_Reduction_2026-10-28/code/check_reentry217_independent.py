#!/usr/bin/env python3
"""Finite, exhaustive local proof of the U218 -> U217 reentry fold.

No parent runtime/source/compiler is imported. The old machine's invariant
is established by exhaustive five-cell induction. Every allowed local frame
then has a positive-length common endpoint in both machines, with exactly
equal whole tape and head; cells outside the frame are opaque.
"""
from pathlib import Path
import argparse,hashlib,itertools,json

def need(ok,msg):
    if not ok:raise ValueError(msg)

def read(path,count):
    result={};starts=[]
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):starts.append(line);continue
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        need((q,b)not in result and b in(0,1)and w in(0,1)and d in('L','R'),'bad row')
        result[q,b]=(w,1 if d=='R'else-1,z)
    states={q for q,b in result}
    need(starts==['#! start 0'],'start header')
    need(len(states)==count and set(result)=={(q,b)for q in states for b in(0,1)},'census')
    need(0 in states and {z for w,d,z in result.values()}-states=={254},'start/halt closure')
    return result,states

def invariant(q,h,tape):return q!=112 or tape[h+1]==0
def rename(q):return 134 if q==112 else q

def advance(table,q,tape,count):
    tape=dict(tape);head=0;trace=[]
    for j in range(count):
        need(q!=254,'intermediate halt')
        need(head in tape,'read of opaque exterior')
        bit=tape[head];w,d,z=table[q,bit]
        trace.append([q,head,bit,w,d,z]);tape[head]=w;head+=d;q=z
    return q,head,tape,trace

def verify(old,new,states):
    need(new=={(q,b):(w,d,rename(z))for(q,b),(w,d,z)in old.items()if q!=112},'not exact 112->134 quotient')
    incoming=sorted((q,b,w,d,z)for(q,b),(w,d,z)in old.items()if z==112)
    need(incoming==[(172,0,0,-1,112)],'invariant entrance differs')
    allowed=0;counts={};examples={}
    for q in sorted(states):
        for bits in itertools.product((0,1),repeat=5):
            tape=dict(zip(range(-2,3),bits))
            if not invariant(q,0,tape):continue
            allowed+=1;w,d,z=old[q,tape[0]];after=dict(tape);after[0]=w
            need(invariant(z,d,after),'old invariant not one-step inductive')
            n=5 if q==112 and tape[0]==1 else 1
            m=3 if q==112 else 1
            oq,oh,ot,otr=advance(old,q,tape,n)
            nq,nh,nt,ntr=advance(new,rename(q),tape,m)
            need((rename(oq),oh,ot)==(nq,nh,nt),('rendezvous mismatch',q,bits,otr,ntr))
            counts[f'{n}:{m}']=counts.get(f'{n}:{m}',0)+1
            if q==112:
                k=f'{tape[0]}:{tape[2]}'
                examples.setdefault(k,{'read':tape[0],'right2':tape[2],'old_trace':otr,'new_trace':ntr,'endpoint':[oq,oh]})
    return {'status':'EXHAUSTIVE_REENTRY_BISIMULATION_PASS','working_states':[218,217],
            'old_invariant':'q=112 implies tape[head+1]=0','invariant_initial_tapes':'all binary tapes at state0',
            'invariant_incoming':incoming,'removed':112,'representative':134,
            'all_radius2_frames':len(states)*32,'admitted_frames':allowed,'durations':counts,
            'local_examples':examples,'opaque_exterior_never_read_or_written':True,
            'mathematical_consequence':'By induction on paired rendezvous blocks: equal tape/head and q_new=rename(q_old). Every block has 1<=old_steps<=5 and 1<=new_steps<=3; no interior halt occurs. Each old or new finite halt therefore corresponds to a halt of the other machine. This holds for every initial tape in state0 and formalizes in PA.',
            'proof_assistant_kernel_certificate':False}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('old',type=Path);p.add_argument('new',type=Path);p.add_argument('--output',type=Path);a=p.parse_args()
    old,states=read(a.old,218);new,_=read(a.new,217);r=verify(old,new,states)
    tests=[]
    for name,key,value in [('wrong redirect',(172,0),(0,-1,135)),('wrong selector',(134,0),(0,1,90)),('wrong long endpoint',(218,1),(1,1,90))]:
        bad=dict(new);bad[key]=value
        try:verify(old,bad,states)
        except ValueError:tests.append({'mutation':name,'rejected':True})
        else:raise ValueError('bad mutation passed')
    r['negative_controls']=tests;r['sha256']={k:hashlib.sha256(v.read_bytes()).hexdigest()for k,v in [('old',a.old),('new',a.new)]}
    s=json.dumps(r,indent=2)+'\n'
    if a.output:a.output.write_text(s)
    print(s,end='')
if __name__=='__main__':main()

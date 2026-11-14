#!/usr/bin/env python3
"""Check the guarded contextual split/reentry used by the U213 candidate.

The unaccepted allocator table is not asserted to be semantically correct.
We form a canonical reference with a fresh state500, whose direct actions
are0R90 and1R61, reached only by146/read0. The repaired214 table replaces
that fresh state by existing182. Its extra local zero path preserves the
whole tape and head. The proof is independent of the source semantics.
"""
from pathlib import Path
import argparse,hashlib,itertools,json

def need(ok,why):
    if not ok:raise ValueError(why)

def table(path):
    T={};starts=[]
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):starts.append(int(line[9:]));continue
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        need((q,b)not in T and b in(0,1)and w in(0,1)and d in('L','R'),'invalid row')
        T[q,b]=(w,1 if d=='R'else-1,z)
    need(starts==[0],'wrong initial state')
    states={q for q,b in T}
    need(set(T)=={(q,b)for q in states for b in(0,1)},'partial table')
    need({z for w,d,z in T.values()}-states=={254},'target closure')
    return T

def encode(T):
    return ('#! start 0\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(T.items()))).encode()

def canonical_reference(raw):
    need(len(raw)==428 and 500 not in{q for q,b in raw},'wrong raw allocation')
    need(raw[146,0]==(0,1,150),'unexpected bad contextual alias')
    C=dict(raw);C[146,0]=(0,1,500);C[500,0]=(0,1,90);C[500,1]=(1,1,61)
    return C

def project(q):return 182 if q==500 else q

def run(T,q,tape,n):
    h=0;t=dict(tape);trace=[]
    for _ in range(n):
        need(q!=254,'internal halt');need(h in t,'opaque exterior read')
        b=t[h];w,d,z=T[q,b];trace.append([q,h,b,w,d,z]);t[h]=w;h+=d;q=z
    return(q,h,t),trace

def local(C,R):
    need([(q,b,*act)for(q,b),act in C.items()if act[2]==500]==[(146,0,0,1,500)],'left-zero guard is not established')
    cases=[]
    for bit,steps in[(0,5),(1,1)]:
        initial={-1:0,0:bit}
        a,oldtrace=run(C,500,initial,1);b,newtrace=run(R,182,initial,steps)
        need(a==b,'local full-tape endpoints differ');need(a[2]==initial,'local tape not restored')
        cases.append({'scanned':bit,'known_left':0,'old_steps':1,'new_steps':steps,'old_trace':oldtrace,'new_trace':newtrace,'endpoint':[a[0],a[1]],'opaque_exterior_unread':True,'whole_tape_preserved':True})
    return cases

def exhaustive(C,R):
    states={q for q,b in C};count=0;counts={}
    for q in sorted(states):
        for bits in itertools.product((0,1),repeat=5):
            initial=dict(zip(range(-2,3),bits))
            if q==500 and initial[-1]!=0:continue
            w,d,z=C[q,initial[0]];old=dict(initial);old[0]=w
            need(z!=500 or old[d-1]==0,'old invariant not inductive')
            n=5 if q==500 and initial[0]==0 else 1
            end,_=run(R,project(q),initial,n)
            need(end==(project(z),d,old),'exhaustive simulation failed')
            count+=1;counts[str(n)]=counts.get(str(n),0)+1
    return {'admissible_radius2_frames':count,'new_steps_counts':counts}

def verify(raw,R,U):
    C=canonical_reference(raw)
    expected={(q,b):(w,d,project(z))for(q,b),(w,d,z)in C.items()if q!=500}
    need(R==expected,'repaired214 is not exact contextual fold')
    need(U=={(q,b):(w,d,75 if z==50 else z)for(q,b),(w,d,z)in R.items()if q!=50},'U213 is not exact seven-zero deletion')
    need(R[34,0]==(0,-1,50) and R[50,0]==(0,-1,75) and R[50,1]==(1,-1,2),'unexpected eight-zero recognizer')
    need(len(C)==430 and len(R)==428 and len(U)==426,'wrong state counts')
    cases=local(C,R);coverage=exhaustive(C,R)
    negative=[]
    for name,key,value,side in[
        ('wrong predecessor write',(146,0),(1,1,500),'old'),
        ('wrong five-step exit',(151,0),(0,1,19),'new'),
        ('wrong reused one write',(182,1),(0,1,61),'new')]:
        c=dict(C);r=dict(R)
        (c if side=='old'else r)[key]=value
        try:local(c,r)
        except ValueError as e:negative.append({'name':name,'rejected':True,'reason':str(e)})
        else:raise ValueError('negative control accepted')
    return C,{'status':'CONTEXT_REENTRY_REPAIR_PASS','reference_states':215,'repaired_states':214,'final_states':213,'canonical_state':500,'representative':182,'changed_incoming':[146,0,0,1,182],'old_invariant':'state500 implies the immediately preceding cell is0','initial_tapes':'all binary tapes from state0','local_cases':cases,**coverage,'negative_controls':negative,'proof':'Induct on old steps using the left-zero invariant; one old step is matched by one or five new steps, with identical complete tape, head, and projected state, and no internal halt. Positive bounded blocks give both halting directions. Formalizable in PA; not proof-assistant kernel checked.','seven_zero_claim':'Only exact literal construction is checked here. The seven-zero deletion is source-specific and requires the separate arbitrary-natural whole-primitive runtime proof and blank-start calibration.'}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('raw',type=Path);ap.add_argument('repaired',type=Path);ap.add_argument('final',type=Path);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--reference',type=Path);a=ap.parse_args()
    C,report=verify(table(a.raw),table(a.repaired),table(a.final))
    report['input_sha256']={name:hashlib.sha256(path.read_bytes()).hexdigest()for name,path in [('raw_allocation',a.raw),('repaired214',a.repaired),('final213',a.final)]}
    report['canonical_reference_sha256']=hashlib.sha256(encode(C)).hexdigest()
    if a.reference:a.reference.write_bytes(encode(C))
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()

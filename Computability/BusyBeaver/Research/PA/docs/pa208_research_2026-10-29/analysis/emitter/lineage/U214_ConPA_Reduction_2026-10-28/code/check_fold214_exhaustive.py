#!/usr/bin/env python3
"""Independently certify the source-independent 215 -> 214 state fold.

The sole guard is: state 156 scans a cell whose immediate left neighbor is
zero. Every entrance establishes it. The candidate reuses state 182 and
its existing predecessor-sensitive dispatcher, so no retained action other
than the sole incoming target changes. All exterior tape is arbitrary.
"""
from pathlib import Path
import argparse,hashlib,itertools,json

def require(ok,msg):
    if not ok:raise ValueError(msg)

def read_table(path,count):
    table={};headers=[]
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):headers.append(line);continue
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        require(q>=0 and z>=0 and b in(0,1)and w in(0,1)and d in('L','R'),'invalid action')
        require((q,b)not in table,'duplicate row');table[q,b]=(w,1 if d=='R'else-1,z)
    states={q for q,b in table}
    require(headers==['#! start 0'],'invalid start header')
    require(len(states)==count and set(table)=={(q,b)for q in states for b in(0,1)},'incorrect census')
    require(0 in states and {z for w,d,z in table.values()}-states=={254},'incorrect target closure')
    return table,states

def project(q):return 182 if q==156 else q
def invariant(q,h,t):return q!=156 or t[h-1]==0

def local_check(old,new,states):
    admitted=0;counts={};examples={}
    for q in sorted(states):
        for bits in itertools.product((0,1),repeat=5):
            tape=dict(zip(range(-2,3),bits))
            if not invariant(q,0,tape):continue
            admitted+=1;b=tape[0];w,d,z=old[q,b];wanted=dict(tape);wanted[0]=w
            require(invariant(z,d,wanted),('noninductive old invariant',q,bits))
            ticks=5 if(q,b)==(156,0)else 1
            nq,nh,nt=project(q),0,dict(tape);trace=[]
            for j in range(ticks):
                require(nq!=254,'premature halt')
                require(nh in nt,'opaque exterior read')
                nb=nt[nh];nw,nd,nz=new[nq,nb]
                trace.append([nq,nh,nb,nw,nd,nz]);nt[nh]=nw;nh+=nd;nq=nz
            require((nq,nh,nt)==(project(z),d,wanted),('local simulation failure',q,bits,trace))
            counts[str(ticks)]=counts.get(str(ticks),0)+1
            if q==156:examples.setdefault(str(b),{'read':b,'left_bit':tape[-1],'old_action':[w,d,z],'candidate_trace':trace,'candidate_steps':ticks})
    return admitted,counts,examples

def verify(old,new,states):
    require(new=={(q,b):(w,d,project(z))for(q,b),(w,d,z)in old.items()if q!=156},'incorrect literal quotient')
    incoming=sorted((q,b,*act)for(q,b),act in old.items()if act[2]==156)
    require(incoming==[(210,0,0,1,156)],'guard predecessor mismatch')
    admitted,counts,examples=local_check(old,new,states)
    return {'status':'U214_EXHAUSTIVE_GUARDED_FOLD_PASS','old_working_states':215,'new_working_states':214,
            'fold':{'removed':156,'representative':182},'old_invariant':'q=156 implies tape[head-1]=0',
            'incoming_guard':incoming,'initial_state':0,'initial_tapes':'ALL_BINARY_TAPES',
            'all_radius2_frames':len(states)*32,'admissible_frames':admitted,
            'old_steps_per_block':1,'new_steps_counts':counts,'special_cases':examples,
            'time_bounds':'old halt at n implies new halt at some m with n<=m<=5n; new halt at m implies old halt at some n<=m',
            'proof':'Induction using the old invariant and checked full-tape endpoint equality. Every block has positive length, preserves head and the projected state, and has no internal halt. Thus finite halting is equivalent on every initial tape in state0; this proof is formalizable in PA.',
            'proof_assistant_kernel_certificate':False}

def controls(old,new,states):
    rejected=[]
    def check(name,a,b):
        try:local_check(a,b,states)
        except ValueError as e:rejected.append({'name':name,'status':'REJECTED','reason':str(e)[:160]})
        else:raise ValueError('mutation accepted: '+name)
    # These controls enter the exhaustive local proof directly, so rejection
    # cannot be caused solely by an exact-table or hash mismatch.
    a=dict(old);b=dict(new);a[210,0]=(1,1,156);b[210,0]=(1,1,182)
    check('wrong predecessor write breaks invariant',a,b)
    b=dict(new);b[182,0]=(0,-1,133)
    check('wrong reused selector breaks simulation',old,b)
    b=dict(new);b[151,0]=(0,1,19)
    check('wrong five-step exit breaks simulation',old,b)
    b=dict(new);b[182,1]=(0,1,61)
    check('wrong shared write breaks tape equality',old,b)
    return rejected

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('old',type=Path);p.add_argument('new',type=Path);p.add_argument('--output',type=Path);a=p.parse_args()
    old,states=read_table(a.old,215);new,_=read_table(a.new,214);result=verify(old,new,states)
    result['negative_controls']=controls(old,new,states)
    result['input_sha256']={k:hashlib.sha256(path.read_bytes()).hexdigest()for k,path in [('old',a.old),('new',a.new)]}
    txt=json.dumps(result,indent=2)+'\n'
    if a.output:a.output.write_text(txt)
    print(txt,end='')
if __name__=='__main__':main()

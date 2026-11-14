#!/usr/bin/env python3
"""Independent opaque-exterior simulation check for deleting native156.

This checker is intentionally independent of the allocator and runtime
engine. Two cells suffice: the entry writes zero immediately to the left,
and the scanned symbol is either0or1. No exterior cell may be read.
"""
import argparse,hashlib,json
from pathlib import Path

def need(p,m):
    if not p:raise ValueError(m)

def table(p):
    T={};starts=[]
    for l in p.read_text().splitlines():
        if l.startswith('#! start '):starts.append(int(l[9:]));continue
        if not l or l.startswith('#'):continue
        q,b,w,d,z=l.split();q,b,w,z=map(int,(q,b,w,z))
        need((q,b)not in T and b in(0,1)and w in(0,1)and d in('L','R'),'invalid row')
        T[q,b]=(w,1 if d=='R'else-1,z)
    need(starts==[0],'wrong start')
    states={q for q,b in T}
    need(set(T)=={(q,b)for q in states for b in(0,1)},'partial table')
    need({z for w,d,z in T.values()}-states=={254},'bad target closure')
    return T

def run(T,q,tape,n):
    t=dict(tape);h=0;trace=[]
    for _ in range(n):
        need(q!=254,'halt in local block');need(h in t,'read of opaque exterior')
        b=t[h];w,d,z=T[q,b];trace.append([q,h,b,w,d,z]);t[h]=w;h+=d;q=z
    need(q!=254,'halt at local endpoint')
    return(q,h,t),trace

def expected_candidate(O):
    return{(q,b):(w,d,182 if z==156 else z)for(q,b),(w,d,z)in O.items()if q!=156}

def verify(O,N):
    need(len(O)==430 and len(N)==428,'wrong census')
    need([(q,b,w,d)for(q,b),(w,d,z)in O.items()if z==156]==[(210,0,0,1)],'wrong predecessor guard')
    need(N==expected_candidate(O),'candidate is not the exact fold')
    cases=[]
    for b,newsteps in [(0,5),(1,1)]:
        tape={-1:0,0:b};end0,tr0=run(O,156,tape,1);end1,tr1=run(N,182,tape,newsteps)
        need(end0==end1,'local endpoints differ')
        need(end0[2]==tape,'local tape changed')
        cases.append({'scanned':b,'left_symbol':0,'old_steps':1,'new_steps':newsteps,'old_trace':tr0,'new_trace':tr1,'endpoint_state':end0[0],'endpoint_head':end0[1],'tape_restored':True,'arbitrary_exterior':True})
    return cases

def controls(O,N):
    result=[]
    tests=[]
    a=dict(O);a[210,0]=(1,1,156);tests.append(('entry writes wrong tag',a,expected_candidate(a),'wrong predecessor guard'))
    a=dict(O);a[151,0]=(0,1,91);tests.append(('shared helper sends zero case to wrong state',a,expected_candidate(a),'local endpoints differ'))
    a=dict(O);a[67,0]=(1,1,151);tests.append(('shared helper changes the tag cell',a,expected_candidate(a),'local endpoints differ'))
    b=dict(N);b[210,0]=(0,1,183);tests.append(('wrong redirection target',O,b,'candidate is not the exact fold'))
    for label,a,b,expected in tests:
        try:verify(a,b)
        except ValueError as e:
            need(str(e)==expected,('unexpected rejection',label,str(e),expected));result.append({'control':label,'rejected':True,'reason':str(e)})
        else:raise ValueError('negative control accepted: '+label)
    return result

def main():
    p=argparse.ArgumentParser();p.add_argument('old',type=Path);p.add_argument('new',type=Path);p.add_argument('--output',type=Path);a=p.parse_args()
    O,N=table(a.old),table(a.new);cases=verify(O,N);negative=controls(O,N)
    result={'status':'GUARDED_ROLE214_FOLD_PASS','input_sha256':hashlib.sha256(a.old.read_bytes()).hexdigest(),'output_sha256':hashlib.sha256(a.new.read_bytes()).hexdigest(),'old_working_states':215,'new_working_states':214,'removed_state':156,'only_changed_retained_row':[210,0,0,1,182],'cases':cases,'negative_controls':negative,'scope':'Exact bounded stuttering equivalence for all runs from state0 on arbitrary initial tape, using the stated left-zero invariant. Logical calibration and source implementation are separate.'}
    if a.output:a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()

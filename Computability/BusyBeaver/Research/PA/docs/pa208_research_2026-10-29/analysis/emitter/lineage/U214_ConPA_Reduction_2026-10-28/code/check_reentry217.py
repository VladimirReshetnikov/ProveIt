#!/usr/bin/env python3
"""Independent finite local proof of U218 -> U217 by removing state112.

The checker uses only table rows and local cells proven to be present.
An unlisted cell is opaque: reading it is fatal. Thus every successful
comparison holds for arbitrary common exterior tape, not sampled windows.
"""
import argparse,hashlib,json
from pathlib import Path

OLD_SHA='366cf96800bd4299de831355a80092394462278f0b62db1e19c167ca5f8b2a30'

def need(p,m):
    if not p:raise ValueError(m)

def table(p):
    T={};starts=[]
    for l in p.read_text().splitlines():
        if l.startswith('#! start '):starts.append(int(l[9:]));continue
        if not l or l.startswith('#'):continue
        q,b,w,d,z=l.split();q,b,w,z=map(int,(q,b,w,z))
        need((q,b)not in T and b in(0,1)and w in(0,1)and d in('L','R'),'invalid table row')
        T[q,b]=(w,1 if d=='R'else-1,z)
    need(starts==[0],'wrong start')
    states={q for q,b in T}
    need(set(T)=={(q,b)for q in states for b in(0,1)},'partial table')
    need({z for w,d,z in T.values()}-states=={254},'bad target closure')
    return T

def run(T,q,tape,n):
    tape=dict(tape);h=0;trace=[]
    for _ in range(n):
        need(q!=254,'halt inside simulated block')
        need(h in tape,'read of opaque exterior')
        b=tape[h];w,d,z=T[q,b];trace.append([q,h,b,w,d,z]);tape[h]=w;h+=d;q=z
    need(q!=254,'halt at local endpoint')
    return(q,h,tape),trace

def main():
    p=argparse.ArgumentParser();p.add_argument('old',type=Path);p.add_argument('new',type=Path);p.add_argument('--output',type=Path);a=p.parse_args()
    need(hashlib.sha256(a.old.read_bytes()).hexdigest()==OLD_SHA,'not primary U218')
    O,N=table(a.old),table(a.new)
    need(len(O)==436 and len(N)==434,'wrong state counts')
    preds=[(q,b,w,d)for(q,b),(w,d,z)in O.items()if z==112]
    need(preds==[(172,0,0,-1)],'additional entry into deleted state')
    expected={(q,b):(w,d,134 if z==112 else z)for(q,b),(w,d,z)in O.items()if q!=112}
    need(N==expected,'candidate contains another change')
    # At entry to112, rightcell is0, written by its sole predecessor.
    # Cases partition all possible scanned bits and all read exterior bits.
    cases=[]
    for label,tape,old_n,new_n in[
        ('scanned0',{0:0,1:0},1,3),
        ('scanned1_right2zero',{0:1,1:0,2:0},5,3),
        ('scanned1_right2one',{0:1,1:0,2:1},5,3),
    ]:
        end1,tr1=run(O,112,tape,old_n);end2,tr2=run(N,134,tape,new_n)
        need(end1==end2,'different local endpoint')
        need(end1[2]==tape,'local tape not restored')
        cases.append({'case':label,'initial_local_cells':tape,'old_steps':old_n,'new_steps':new_n,'old_trace':tr1,'new_trace':tr2,'endpoint_state':end1[0],'endpoint_head':end1[1],'arbitrary_exterior':True,'tape_unchanged':True})
    result={'status':'TWO_SIDED_LOCAL_REENTRY_PROOF_PASS','input_sha256':OLD_SHA,'output_sha256':hashlib.sha256(a.new.read_bytes()).hexdigest(),'old_working_states':218,'new_working_states':217,'removed_state':112,'only_retained_changed_row':[172,0,0,-1,134],'unique_old_incoming_row':[172,0,0,-1,112],'cases':cases,'whole_block_lengths_including_predecessor':[[2,4],[6,4],[6,4]],'scope':'All runs from state0 on arbitrary initial binary tape; conditional on the elementary synchronized-block induction in proof_reentry217.tex. No new kernel proof object.'}
    if a.output:a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()

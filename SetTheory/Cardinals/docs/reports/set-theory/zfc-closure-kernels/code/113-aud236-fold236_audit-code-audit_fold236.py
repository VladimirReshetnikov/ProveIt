#!/usr/bin/env python3
"""Independent pinned-table audit of the newly published236 local fold.

No upstream proof or discovery module is imported. Every unmentioned tape cell
is left arbitrary. This proves the local rotated237-to236 transformation;
source calibration and binary runtime are independently reviewed by the parent.
"""
from pathlib import Path
from hashlib import sha256
import json
ROOT=Path(__file__).resolve().parents[1]
def need(p,why):
    if not p: raise ValueError(why)
def parse(name,pin=None,start_required=True):
    raw=(ROOT/'input'/name).read_bytes();h=sha256(raw).hexdigest()
    if pin:need(h==pin,('hash mismatch',name,h))
    table={};starts=[]
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):starts.append(int(line[9:]))
        elif line and not line.startswith('#'):
            q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
            need(b in (0,1) and w in (0,1) and d in ('L','R'),'invalid row')
            need((q,b) not in table,'duplicate row')
            table[q,b]=(w,1 if d=='R' else -1,z)
    if start_required:need(starts==[95],('start declaration',name,starts))
    states={q for q,b in table}
    need(set(table)=={(q,b)for q in states for b in(0,1)},'not total binary')
    need({z for w,d,z in table.values()}-states=={254},'wrong halt set')
    return table,h
A,ha=parse('original237.tm','a3c4407f30e2e2139af87c6a91948c518134855841a28eb85b1d81bcfd026c9a')
M,hm=parse('rotated237.tm','da0b3d1fdd74d56482b9d231119bbbaccdbcadc78e7b7df72c3a734a3a808724')
N,hn=parse('machine236.tm','ff059535876bc9e1e1e63174ebfd1c10a91c1a818ba0c3f8c4ef2ac51a3cfcc3')
O238,h238=parse('original238.tm','ab1f12ceb0b1cbc167977286652dd3be3407e9b24fcd3f8e7c9ac630166514b9',False)
need(len(A)==len(M)==474 and len(N)==472,'wrong row counts')
need({q for q,b in N}=={q for q,b in M}-{223},'wrong deletion')
phi=lambda q:182 if q==223 else q
rotation={(177,0):((0,1,165),(0,1,185)),
          (177,1):((1,1,185),(1,1,212)),
          (185,0):((0,1,192),(0,1,165)),
          (185,1):((1,1,212),(1,1,192))}
need(set(A)==set(M),'rotation changed state set')
need({k:(A[k],M[k]) for k in A if A[k]!=M[k]}==rotation,'unexpected rotation edit')
ordinary=0
for (q,b),(w,d,z) in M.items():
    if q not in (182,223):
        need(N[q,b]==(w,d,phi(z)),('ordinary row fails',q,b));ordinary+=1
need(ordinary==470,'ordinary census')
arrivals={}
for q,tag,caller in [(182,1,(76,1)),(223,0,(237,0))]:
    incoming={k:row for k,row in M.items() if row[2]==q}
    need(incoming=={caller:(tag,1,q)},('predecessor guard fails',q,incoming))
    arrivals[q]={'caller':list(caller),'left_bit':tag}
blocks=[]
for q in (182,223):
    for bit in (0,1):
        cells={-1:arrivals[q]['left_bit'],0:bit};state=phi(q);head=0;trace=[]
        for step in range(3):
            need(head in cells,('arbitrary cell would be read',q,bit,head))
            read=cells[head];write,move,target=N[state,read]
            need(write==read,('a bit changes',q,bit,step))
            need(target!=254,'interior halt')
            trace.append([state,head,read,write,move,target])
            state=target;head+=move
        w,d,z=M[q,bit]
        need(w==bit and (state,head)==(phi(z),d),('endpoint mismatch',q,bit))
        blocks.append({'old_row':[q,bit],'guard':{'left_bit':arrivals[q]['left_bit']},'old_row_value':[w,d,z],
                       'new_steps':3,'trace':trace,'entire_tape_preserved':True})
# Verify literal commutation of the old235 fold with the four-row rotation.
def rotate(T):
    V=dict(T)
    for k,(before,after) in rotation.items():need(V[k]==before,('rotate precondition',k));V[k]=after
    return V
def fold235(T):
    f=lambda z:98 if z==235 else z
    V={(q,b):(w,d,f(z))for(q,b),(w,d,z)in T.items()if q!=235}
    V[98,0]=(0,-1,240);V[240,1]=(1,-1,87)
    return V
need(fold235(O238)==A,'old235 fold baseline mismatch')
need(rotate(fold235(O238))==fold235(rotate(O238))==M,'rotation and old235 fold do not commute')
def fold223(T):
    V={(q,b):(w,d,phi(z))for(q,b),(w,d,z)in T.items()if q!=223}
    V[182,0]=(0,-1,198);V[182,1]=(1,-1,210)
    return V
need(fold223(fold235(rotate(O238)))==fold235(fold223(rotate(O238)))==N,'the two binary folds do not commute')

# Explain exactly which new row enables the fourth exceptional block.
without_rotation=dict(A)
without_rotation[182,0]=(0,-1,198);without_rotation[182,1]=(1,-1,210)
state=182;head=0;cells={-1:1,0:1}
for _ in range(3):
    w,d,z=without_rotation[state,cells[head]];need(w==cells[head],'control write')
    state=z;head+=d
need((state,head)==(185,1) and A[182,1]==(1,1,212),'rotation dependency control')
result={'status':'PASS_INDEPENDENT_PINNED_ALL_TAPE_LOCAL_FOLD_236',
        'original237_sha256':ha,'rotated237_sha256':hm,'machine236_sha256':hn,
        'old_states':237,'new_states':236,'start':95,'halt':254,'deleted':223,'retained':182,
        'complete_arrival_guards':arrivals,'ordinary_rows':ordinary,'exceptional_blocks':blocks,
        'arbitrary_initial_tape_and_head':True,'old_steps_per_block':1,'new_step_bounds':[1,3],
        'exact_tape_and_head_at_halt':True,
        'source_rotation_rows':[{'row':list(k),'before':list(v[0]),'after':list(v[1])}for k,v in rotation.items()],
        'old235_fold_commutes_with_source_rotation':True,
        'folds_235_to98_and_223_to182_commute_after_rotation':True,
        'without_source_rotation_three_step_control':{'old_row':[182,1],'old_target':212,'new_endpoint_state':185,'new_endpoint_head':1},
        'scope':'Ordinary all-tape positive-block proof of the local rotated237-to236 fold; four source-rotation rows are identified but their semantic justification is a separate source proof.'}
print(json.dumps(result,indent=2))

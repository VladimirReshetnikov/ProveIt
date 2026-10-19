#!/usr/bin/env python3
"""All-tape positive-block proof for the final 228→227 role reassignment.

Only the predecessor cell and current cell are fixed. Unknown outside cells
are never read or written, so the finite traces prove their claimed effects
for every outside tape. No bounded execution of the whole machine is used.
"""
from pathlib import Path
import argparse,json,hashlib
from build227 import read_table,sha
HERE=Path(__file__).resolve().parent
def incoming(t,target):return sorted((q,b,w,d) for(q,b),(w,d,z) in t.items() if z==target)
def trace(t,start,previous,current,goal):
    tape={-1:previous,0:current};initial=dict(tape);q=start;h=0;seen=set();rows=[]
    for tick in range(30):
        if(q,h)==(goal,1):
            assert tick>0 and tape==initial
            return {'steps':tick,'trace':rows,'endpoint_state':q,'endpoint_head':h,'final_known_cells':tape}
        assert h in tape,('would inspect an arbitrary outside cell',q,h)
        assert(q,h,tuple(sorted(tape.items()))) not in seen,'cycle'
        seen.add((q,h,tuple(sorted(tape.items()))));bit=tape[h];w,d,z=t[q,bit]
        rows.append({'state':q,'head':h,'read':bit,'write':w,'direction':d,'next_state':z})
        tape[h]=w;q,h=z,h+d
    raise ValueError('A proposed local block failed to synchronize')
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--generated',type=Path,default=HERE/'generated');ap.add_argument('--out',type=Path,default=HERE/'role_proof.json');a=ap.parse_args()
    p=a.generated/'04_rotated_basis228/table_k230labels.tm';q=a.generated/'05_k227/table_k230labels.tm'
    old=read_table(p);new=read_table(q)
    assert len(old)==456 and len(new)==454
    assert set(old)-set(new)=={(175,0),(175,1)}
    old_in={target:incoming(old,target) for target in(150,152,175)}
    assert old_in[150]==[(183,0,0,1),(201,0,0,1)]
    assert old_in[152]==[(119,1,1,1)]
    assert old_in[175]==[(155,1,1,1),(176,1,1,1),(184,0,0,1)]
    # These incoming-row facts inductively establish the old-machine tags
    # from its start0, independently of the contents of the rest of the tape.
    expected_changes={(150,1):(1,-1,173),(152,0):(0,-1,159),(152,1):(1,-1,169),
                      (155,1):(1,1,150),(176,1):(1,1,150),(184,0):(0,1,152)}
    actual={row:new[row] for row in new if old[row]!=new[row]}
    assert actual==expected_changes
    cases=[]
    # name, old state, new state, predecessor bit, child states for read0/1
    roles=[('pp',150,150,0,(90,90)),('pi',175,150,1,(90,61)),
           ('zi',175,152,0,(19,61)),('W',152,152,1,(155,171))]
    for name,oldq,newq,pred,goals in roles:
        for bit in(0,1):
            left=trace(old,oldq,pred,bit,goals[bit]);right=trace(new,newq,pred,bit,goals[bit])
            cases.append({'role':name,'old_entry':oldq,'new_entry':newq,'predecessor':pred,'read':bit,
                          'old_block':left,'new_block':right})
    # A changed incoming transition writes the context bit and moves right,
    # so its two successor states satisfy the asserted role relation.
    redirect_cases=[]
    for row in[(155,1),(176,1),(184,0)]:
        w,d,z=old[row];nw,nd,nz=new[row];assert(w,d)==(nw,nd)==(row[1],1) and z==175
        assert nz==(150 if w else 152)
        redirect_cases.append({'row':row,'predecessor_created':w,'old_target':z,'new_target':nz})
    receipt={'status':'ALL_TAPES_POSITIVE_BLOCK_ROLE_EQUIVALENCE_PASS','old_table_sha256':sha(p),'new_table_sha256':sha(q),
        'working_states':[228,227],'start_state':0,'halt_state':230,'deleted_state':175,
        'old_tag_invariant':{'150':'tape[head-1]=0','152':'tape[head-1]=1'},
        'invariant_initialization':'Start0 is outside the constrained states.',
        'invariant_induction':'Every incoming transition into150 or152 writes the required bit and moves right.',
        'incoming_rows':old_in,'relation':'Old175 maps to new150 when the predecessor is1, and to new152 when it is0; all other old states map identically. Related configurations have identical entire tapes and heads.',
        'ordinary_rows':'Every other transition is literally identical, except the three checked incoming redirects.',
        'incoming_redirects':redirect_cases,'cases':cases,'verified_cases':len(cases),
        'maximum_old_block_steps':max(c['old_block']['steps'] for c in cases),'maximum_new_block_steps':max(c['new_block']['steps'] for c in cases),
        'scope':'Exact halting equivalence of the rotated228 basis and227 from start0 on arbitrary tapes. The source rotations, H identity, and earlier native folds have separate certificates.'}
    a.out.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:receipt[k] for k in['status','working_states','verified_cases','maximum_old_block_steps','maximum_new_block_steps','old_table_sha256','new_table_sha256']},indent=2))
    for c in cases:print(c['role'],c['read'],c['old_block']['steps'],c['new_block']['steps'])
if __name__=='__main__':
    if not __debug__:raise RuntimeError('Run with assertions enabled')
    main()

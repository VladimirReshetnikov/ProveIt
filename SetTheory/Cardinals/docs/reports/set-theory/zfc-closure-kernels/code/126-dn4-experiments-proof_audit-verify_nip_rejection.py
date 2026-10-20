#!/usr/bin/env python3
"""Replay a concrete failure of the direct NIP state-38 specialization.

This deliberately rejects the patch. It is a literal finite counterexample,
not an argument from bounded testing in favor of a universal machine theorem.
Input: a normalized accepted table with dispatcher84/start0/halt254.
"""
from pathlib import Path
import argparse,hashlib,json

def require(x,message):
    if not x:raise ValueError(message)

def parse(path):
    T={};starts=[]
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):starts.append(int(line[9:]))
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        require((q,b)not in T and b in(0,1)and w in(0,1)and d in('L','R'),'Malformed table')
        T[q,b]=(w,1 if d=='R'else-1,z)
    states={q for q,b in T}
    require(starts==[0]and 0 in states and 254 not in states,'Wrong start/halt')
    require(set(T)=={(q,b)for q in states for b in(0,1)},'Partial table')
    require({z for w,d,z in T.values()}-states=={254},'Wrong terminal state')
    return T

def encode(T):
    return('#! start 0\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(T.items()))).encode()

def frame(pc,values,spares,width=64):
    require(len(pc)<=width and len(values)==9,'Malformed frame')
    ones={-1,width}|{i for i,b in enumerate(pc)if b=='1'}
    physical=[0]*9
    for r,p in enumerate([6,2,0,4,3,7,8,5,1]):physical[p]=values[r]
    cursor=width+1
    for value in physical+spares:
        cursor+=1;ones.update(range(cursor,cursor+value+1));cursor+=value+1
    return ones

def first_next_frame(T,ones):
    q,h=84,0;tape=set(ones);visits=[]
    for k in range(10000):
        require(q!=254,'Unexpected early halt')
        b=int(h in tape);w,d,z=T[q,b]
        if q==38:visits.append([k,h,b,w,d,z])
        if w:tape.add(h)
        else:tape.discard(h)
        h+=d;q=z
        if(q,h)==(84,0)and all((i in tape)==(b=='1')for i,b in enumerate('01011'))and 64 in tape and all(i not in tape for i in range(5,64)):
            return dict(steps=k+1,state=q,head=h,one_cells=sorted(tape),all_other_cells=0,q38_visits=visits)
    raise ValueError('No tested output frame within finite counterexample bound')

def blank_diagnostic(T):
    q,h=0,0;tape=set();visits=0
    for k in range(409835):
        require(q!=254,'Unexpected early blank halt')
        b=int(h in tape);w,d,z=T[q,b]
        if q==38 and b==0:visits+=1
        if w:tape.add(h)
        else:tape.discard(h)
        h+=d;q=z
    return dict(steps=409835,state=q,head=h,one_cells=sorted(tape),q38_zero_visits=visits)

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('reference',type=Path)
    ap.add_argument('--output',type=Path,required=True);ap.add_argument('--candidate-output',type=Path)
    args=ap.parse_args();T=parse(args.reference);N=dict(T)
    edits={(38,0):((0,1,13),(0,1,53)),(38,1):((1,1,53),(1,1,69)),
           (53,0):((0,1,68),(0,1,45)),(53,1):((1,1,69),(1,1,68)),
           (68,0):((0,1,77),(0,1,88))}
    for row,(before,after)in edits.items():require(T[row]==before,'Unexpected reference row');N[row]=after
    initial=frame('01010',[0]*9,[0]);expected_values=[0]*9;expected_values[8]=1
    correct=frame('01011',expected_values,[0,1]);wrong=frame('01011',[0]*9,[0])
    old=first_next_frame(T,initial);new=first_next_frame(N,initial)
    require(old['one_cells']==sorted(correct),'Reference does not perform expected increment')
    require(new['one_cells']==sorted(wrong)and wrong!=correct,'Counterexample did not reproduce')
    oldboot=blank_diagnostic(T);newboot=blank_diagnostic(N)
    require((oldboot['state'],oldboot['head'],len(oldboot['one_cells']))==(84,-5,351),'Reference startup is not calibrated')
    require(oldboot['one_cells']!=newboot['one_cells']or(oldboot['state'],oldboot['head'])!=(newboot['state'],newboot['head']),'Startup diagnostic unexpectedly agrees')
    candidate=encode(N)
    if args.candidate_output:args.candidate_output.write_bytes(candidate)
    result=dict(status='COUNTEREXAMPLE_REPLAY_PASS_PATCH_REJECTED',
        reference_sha256=hashlib.sha256(args.reference.read_bytes()).hexdigest(),candidate_sha256=hashlib.sha256(candidate).hexdigest(),
        checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        changed_rows=[dict(row=row,before=before,after=after)for row,(before,after)in edits.items()],
        input=dict(state=84,head=0,path='01010',header_width=64,logical_registers=[0]*9,spares=[0],one_cells=sorted(initial),all_other_cells=0),
        reference_output=old,rejected_output=new,reference_blank=oldboot,rejected_blank=newboot,
        conclusion='The rejected patch reaches the next clean source frame without incrementing R8 or appending its spare. It also does not inherit the calibrated startup.')
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()if k not in('reference_output','rejected_output','reference_blank','rejected_blank','input')},indent=2))
    print('Primitive durations:',old['steps'],new['steps'],'; startup q38/0 visits:',oldboot['q38_zero_visits'])

if __name__=='__main__':main()

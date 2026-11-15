#!/usr/bin/env python3
"""Compose the ORH source layout with the previously known B history selector.

The exact finite-run transfer is independent of arithmetic/source simulation.
Relocated into this package; only input/output path handling was adapted.
It gives no unconditional Con(PA) calibration absent the parent's calibration.
"""
from pathlib import Path
import argparse, json, hashlib
ROOT=Path(__file__).resolve().parent

def read(p):
    rows={}
    for line in p.read_text().splitlines():
        if not line.strip() or line.startswith('#'):continue
        q,b,w,d,t=line.split();rows[int(q),int(b)]=int(w),1 if d=='R' else -1,int(t)
    return rows

def txt(rows):return ''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {t}\n'for(q,b),(w,d,t)in sorted(rows.items()))
def sha(s):return hashlib.sha256(s.encode()).hexdigest()
def check(old,new):
    delta={(q,b):(old[q,b],new[q,b]) for q,b in old if old[q,b]!=new[q,b]}
    wanted={(87,0):((0,1,301),(0,1,88)),(88,0):((0,1,122),(0,-1,301)),
            (301,0):((0,1,45),(0,1,122)),(301,1):((1,1,103),(1,1,301))}
    assert delta==wanted
    incoming={t:sorted((q,b,w,d)for(q,b),(w,d,u)in old.items()if u==t)for t in(88,301)}
    assert incoming=={88:[(77,1,1,1)],301:[(87,0,0,1)]}
    assert set(q for q,b in old)==set(q for q,b in new) and len(new)==388
    rho=lambda q:88 if q==301 else q
    ordinary=0
    for(q,b),(w,d,t)in old.items():
        if q not in(88,301):
            assert new[rho(q),b]==(w,d,rho(t));ordinary+=1
    cases=[]
    for q,hist in((88,1),(301,0)):
        for bit in(0,1):
            tape={-1:hist,0:bit};state,pos=88,0;w,d,t=old[q,bit]
            goal=(rho(t),d,{-1:hist,0:w});trace=[]
            for step in range(1,6):
                assert pos in tape and state!=254
                before=(state,pos,dict(tape));w,d,state=new[state,tape[pos]];tape[pos]=w;pos+=d
                trace.append(dict(before=before,after=(state,pos,dict(tape))))
                if(state,pos,tape)==goal:break
            else:raise ValueError('local identity failed')
            assert step==(1 if bit else 3 if q==88 else 5)
            cases.append(dict(old_state=q,history=hist,read=bit,steps=step,trace=trace))
    return dict(ordinary_cases=ordinary,exceptional_cases=cases,arbitrary_exterior_unread=True,
                halting_transfer='For every initial tape and head, with initial state 74, Halt(parent) iff Halt(child).',
                quantitative='t <= t_child <= 5*t for every old-prefix endpoint.',
                arithmetic_scope='The finite bounded trace transformations can be proved in iPRA. No complete Con(PA) calibration is supplied here.')

def startup(rows):
    sites=json.loads((ROOT/'PA194ORH/sites.json').read_text());path=sites[25][0]
    physical=[0,0,0,0,0,0,2,0,0]+[1]*26
    head0=-2;expected={-3,46};expected.update(-2+i for i,b in enumerate(path)if b=='1')
    p=47
    for value in physical:p+=1;expected.update(range(p,p+value+1));p+=value+1
    q,head,ones=74,0,set();uses=0
    for step in range(100000):
        if(q,head,ones)==(84,head0,expected):
            return dict(steps=step,state=q,head=head,physical_file=physical,
                        one_cells=sorted(ones),complete_tape_equality=True,selector_entries=uses)
        assert q!=254
        w,d,t=rows[q,int(head in ones)];uses+=int(t==301);(ones.add if w else ones.discard)(head);q=t;head+=d
    raise ValueError('No clean initial frame')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,default=ROOT/'PA194ORHB');args=ap.parse_args()
    old=read(ROOT/'PA194ORH/machine.native.tm');rows=dict(old)
    rows.update({(87,0):(0,1,88),(88,0):(0,-1,301),(301,0):(0,1,122),(301,1):(1,1,301)})
    proof=check(old,rows);boot=startup(rows)
    labels=[74];ix={74:0}
    for q in labels:
        for b in(0,1):
            t=rows[q,b][2]
            if t!=254 and t not in ix:ix[t]=len(labels);labels.append(t)
    assert len(labels)==194
    dense={(ix[q],b):(w,d,194 if t==254 else ix[t])for(q,b),(w,d,t)in rows.items()}
    out=args.output;out.mkdir(exist_ok=True,parents=True)
    for name,r in [('machine.native.tm',rows),('machine.tm',dense)]:
        (out/name).write_text(txt(r))
    (out/'labels.json').write_text(json.dumps(labels+[254])+'\n')
    receipt=dict(name='PA194ORHB',states=194,rows=388,source_sites=len(json.loads((ROOT/'PA194ORH/sites.json').read_text())),
                 startup=boot,parent_native_sha256=sha(txt(old)),native_sha256=sha(txt(rows)),dense_sha256=sha(txt(dense)),
                 known_components='ORH source-address layout plus previously known B dedicated history selector; composition only.',
                 proof=proof)
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items()if k not in('proof','startup')},indent=2));print('startup_steps',boot['steps'])
if __name__=='__main__':main()

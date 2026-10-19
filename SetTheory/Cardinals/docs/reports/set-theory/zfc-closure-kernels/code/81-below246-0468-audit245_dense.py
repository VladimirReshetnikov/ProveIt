"""Independent dense-tape audit of the association-rotation245candidate.

Finite evidence only. The universal source/control-flow and register-frame
induction certificates are separate. This code imports neither their table
parser, simulator, source-expander, nor expected-tape constructor.
"""
from pathlib import Path
from collections import Counter
import json,hashlib,time

HERE=Path(__file__).parent
ROOT=HERE.parent
TABLE=ROOT/'research/rotation245_old.tm'
SOURCE=ROOT/'agent_logic/rotation_candidate_00.json'
PHYSICAL=(6,2,0,4,3,7,8,5,1)
OFFSET=2048
SIZE=8192

def read_table(path):
    rows={}
    for line in path.read_text().splitlines():
        if line.startswith('#') or not line:continue
        q,b,w,d,t=line.split();key=(int(q),int(b))
        assert key not in rows and d in ('L','R')
        rows[key]=(int(w),-1 if d=='L' else 1,int(t))
    states={q for q,b in rows}
    assert len(states)==245 and len(rows)==490
    assert all((q,b) in rows for q in states for b in (0,1))
    assert {t for w,d,t in rows.values()}-states=={254}
    assert 208 not in states
    return rows

def source_sites():
    data=json.loads(SOURCE.read_text());pairs=data['entries']
    sites=[]
    def expand(node,path,ancestors):
        assert node not in ancestors
        e=pairs[str(node)]
        if e[0]=='N':
            expand(e[1],path+'0',ancestors|{node})
            expand(e[2],path+'1',ancestors|{node})
        else:sites.append((path,e[0],e[1]))
    expand(data['root'],'',set())
    assert len(sites)==6460
    physical=[[p,op,PHYSICAL[r] if op in ('CI','CD') else r] for p,op,r in sites]
    assert physical==json.loads((ROOT/'research/rotation245-sites-physical.json').read_text())
    return sites

def paint(pc,h,d,regs,spares):
    tape=bytearray(SIZE)
    tape[OFFSET+h-1]=1
    for i,b in enumerate(pc):tape[OFFSET+h+i]=int(b)
    at=OFFSET+h+d;tape[at]=1;at+=1
    for v in regs+spares:
        assert v>=0
        tape[at+1:at+v+2]=bytes([1])*(v+1);at+=v+2
    assert at<SIZE
    return tape

def suffix_removed(p,bit,count):
    positions=[i for i,b in enumerate(p) if b==bit]
    return '' if len(positions)<count else p[:positions[-count]]

def advance(p):
    n=int(p or '0',2)+1
    if n>=2**len(p):return '',True
    return f'{n:0{len(p)}b}',False

def desired(pc,op,r,regs,spares,d):
    out=list(regs);sp=list(spares);delta=0;overflow=False
    if op=='CH':return None
    if op=='CI':
        out[PHYSICAL[r]]+=1;sp.append(1);nxt,overflow=advance(pc)
    elif op=='CD' and out[PHYSICAL[r]]>0:
        out[PHYSICAL[r]]-=1;delta=1;nxt,overflow=advance(pc)
    elif op=='CD':nxt,overflow=advance(suffix_removed(pc,'0',1))
    elif op=='CB':nxt,overflow=advance(suffix_removed(pc,'0',r))
    elif op=='CC':nxt=suffix_removed(pc,'1',r)
    else:raise AssertionError(op)
    h=-int(overflow);d+=delta+int(overflow)
    return h,paint(nxt,h,d,out,sp)

def bootstrap(T):
    tape=bytearray(SIZE);head=OFFSET;q=95;counts=Counter();lo=head;hi=head
    for tick in range(410735):
        assert 0<head<SIZE-1
        b=tape[head];counts[q,b]+=1;w,d,q=T[q,b];tape[head]=w;head+=d
        lo=min(lo,head);hi=max(hi,head)
    expected=paint('',-5,181,[0,0,0,3,0,0,3,0,0],[1]*167)
    assert (q,head-OFFSET)==(96,-5) and tape==expected
    assert counts[178,0]==counts[178,1]==0
    ones=[i-OFFSET for i,b in enumerate(tape) if b]
    assert len(ones)==351
    return dict(steps=410735,exit_state=96,head=-5,header=176,header_distance=181,
        physical_registers=[0,0,0,3,0,0,3,0,0],spare_count=167,spare_values=1,
        ones=ones,all_other_cells_zero=True,visited_cell_min=lo-OFFSET,
        visited_cell_max=hi-OFFSET,modified_state178_never_visited=True)

def literal_cases(T,sites):
    total=0;steps=0;used=Counter();max_steps=0;max_visits=0
    suites=[(0,[0],[0,1,2,3,5,8,13,21,34]),
            (1,[1],[7,5,3,1,0,2,4,6,8]),
            (17,[2,0,3],[0]*9),
            (53,[0,1],[9,8,7,6,5,4,3,2,1])]
    for slack,spares,base in suites:
        for pc,op,r in sites:
            for positive in ((False,True) if op=='CD' else (None,)):
                regs=base.copy()
                if op=='CD':regs[PHYSICAL[r]]=17 if positive else 0
                d=40+slack;want=desired(pc,op,r,regs,spares,d)
                tape=paint(pc,0,d,regs,spares);q=96;head=OFFSET;visits=0
                for ticks in range(1,200000):
                    assert 0<head<SIZE-1
                    b=tape[head];used[q,b]+=1;w,move,q=T[q,b];tape[head]=w;head+=move
                    if q==254:
                        assert op=='CH';break
                    if q==96:
                        if want is not None and head-OFFSET==want[0] and tape==want[1]:break
                        visits+=1;assert visits<=30,(pc,op,r,'excess intermediate dispatch')
                else:raise AssertionError(('literal fuel',pc,op,r))
                total+=1;steps+=ticks;max_steps=max(max_steps,ticks);max_visits=max(max_visits,visits)
        print('SUITE',slack,total,steps,flush=True)
    assert total==33564 and len(used)==490
    return dict(cases=total,literal_steps=steps,maximum_case_steps=max_steps,
        maximum_intermediate_dispatch_visits=max_visits,distinct_rows=len(used),
        finite_only=True,whole_tape_equality=True,suites=suites)

def main():
    began=time.monotonic();T=read_table(TABLE);sites=source_sites()
    out=dict(status='PASS',table_sha256=hashlib.sha256(TABLE.read_bytes()).hexdigest(),
        source_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        parser_source_mapping_independent=True,bootstrap=bootstrap(T),
        instructions=literal_cases(T,sites),seconds=time.monotonic()-began)
    (HERE/'audit245_dense_result.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='bootstrap'},indent=2))

if __name__=='__main__':main()

#!/usr/bin/env python3
"""Independent finite audit of the pinned public 253-state machine.

Checks actual transition bytes, complete exact boot tape and RM prefix, plus
the upstream affine instruction model on every leaf of the pinned Coq program.
This does not run Coq or internalize its metatheorem in ZFC.
"""
from pathlib import Path
from collections import deque,Counter
import json,hashlib,time
import collect_contexts as c

HERE=Path(__file__).resolve().parent
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def exact_boot():
    tape=set();head=0;q=5
    for step in range(312975):
        w,d,q=c.T0[q,int(head in tape)]
        if w:tape.add(head)
        else:tape.discard(head)
        head+=1 if d=='R' else -1
    assert q==96 and head==-17
    phys=[0,2,0,0,0,0,5,0,0]
    suffix=[0,0,1,0,0,0,0,0,1]+[0]*149
    expect={head-1,head+40};at=head+41
    for v in phys+suffix:
        expect.update(range(at+1,at+v+2));at+=v+2
    assert tape==expect,{'extra':sorted(tape-expect),'missing':sorted(expect-tape)}
    return {'steps':312975,'old_state':q,'compact_state':c.candidate.OLD_TO_COMPACT[q],
            'head':head,'pc':'000','gap':40,'physical_registers':phys,'spare_values':suffix,
            'ones':sorted(tape),'ones_count':len(tape),'full_tape_equal':True}

def inc(P):
    a=list(P);i=len(a)-1
    while i>=0 and a[i]=='1':a[i]='0';i-=1
    if i>=0:a[i]='1'
    return ''.join(a)

def prefix330():
    P='';R=[2]+[0]*8
    for step in range(330):
        n=0;d=0
        while True:
            e=c.nodes[n][int(P[d]) if d<len(P) else 0];d+=1
            if e[0]=='CN':n=e[1]
            else:break
        P=(P+'0'*d)[:d];kind,r=e
        if kind=='CI':R[r]+=1;P=inc(P)
        elif kind=='CD':
            if R[r]:R[r]-=1;P=inc(P)
            else:P=inc(c.ns['strip']('0',1,P))
        elif kind=='CB':P=inc(c.ns['strip']('0',r,P))
        elif kind=='CC':P=c.ns['strip']('1',r,P)
        else:raise AssertionError(('unexpected halt',step))
    assert P=='000' and R==[5,0,0,0,2,0,0,0,0],(P,R)
    return {'rm_steps':330,'pc':P,'logical_registers':R}

def structure():
    states=sorted({q for q,b in c.T0})
    reachable={5};todo=deque([5])
    while todo:
        q=todo.popleft()
        if q==254:continue
        for b in (0,1):
            t=c.T0[q,b][2]
            if t not in reachable:reachable.add(t);todo.append(t)
    assert reachable==set(states)|{254}
    cls={q:0 for q in states};cls[254]=1;rounds=[]
    while True:
        sig={q:tuple((w,d,cls[t]) for b in (0,1) for w,d,t in [c.T0[q,b]]) for q in states}
        groups={};nxt={254:-1}
        for q in states:nxt[q]=groups.setdefault(sig[q],len(groups))
        rounds.append(len(groups))
        if all((cls[p]==cls[q])==(nxt[p]==nxt[q]) for p in states for q in states):break
        cls=nxt
    assert rounds[-1]==253
    return {'working_states':len(states),'binary_rows':len(c.T0),'graph_reachable_working':253,
            'partition_class_counts':rounds,'nontrivial_exact_quotient':False}

def main():
    c.candidate.generate_candidate()
    assert (c.UP/'m253/machine/zfc_253.tm').read_bytes()==c.candidate.generate_candidate()
    c.ns['observe']=lambda *args:None
    result={'upstream_commit':'0d544f2a2e3c18f12278441a74b7879f31cbe856',
      'table_sha256':sha(c.UP/'m253/machine/zfc_253.tm'),
      'program_sha256':sha(c.UP/'m254/coq/tm/Prog254.v'),
      'structure':structure(),'boot':exact_boot(),'rm_prefix':prefix330(),
      'affine_instruction_cases':dict(c.run_all()),
      'scope':'Executable finite/source-model audit; no Coq rebuild and no internal ZFC consistency theorem.'}
    (HERE/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='boot'},indent=2))
    print('Complete boot tape agrees: 178 one cells, with 158 explicitly checked spare blocks.')
if __name__=='__main__':main()

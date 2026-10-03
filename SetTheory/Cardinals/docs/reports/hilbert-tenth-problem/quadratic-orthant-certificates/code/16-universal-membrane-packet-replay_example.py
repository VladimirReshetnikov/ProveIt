#!/usr/bin/env python3
"""Reproduce the accepting example by exact virtual replay and proved macro counts.
This does NOT enumerate its ~7.4e17 physical instructions or membrane steps.
"""
import json
from pathlib import Path
R=Path(__file__).resolve().parent
V=json.loads((R/'virtual3.json').read_text());TM=json.loads((R/'tm_table.json').read_text())
rows=V['rows'];cuts={v:k for k,v in V['tm_cuts'].items()};lab=V['entry'];regs=[6,0,0]
N=64;physical=adds=subpos=subzero=virtual=0;peak=N;trace=[]
while lab!='HALT':
    if lab in cuts and regs[2]==0:
        trace.append(dict(control=cuts[lab],L=regs[0],R=regs[1],encoded_A=N,virtual_instructions=virtual,physical_instructions=physical))
    op,i,*dest=rows[lab];p=(2,3,5)[i];Q,r=divmod(N,p)
    if op=='ADD':aa=2*p*N;ss=(p+1)*N;out=p*N
    elif r==0:aa=2*Q;ss=N+Q;out=Q
    else:aa=N+Q;ss=N+Q;out=N
    physical+=aa+ss+2;adds+=aa;subpos+=ss;subzero+=2
    if op=='ADD':regs[i]+=1;lab=dest[0]
    elif regs[i]:regs[i]-=1;lab=dest[0]
    else:lab=dest[1]
    N=out;assert N==2**regs[0]*3**regs[1]*5**regs[2]
    peak=max(peak,N);virtual+=1
    assert virtual<=1000
trace.append(dict(control='J1',L=regs[0],R=regs[1],encoded_A=N,virtual_instructions=virtual,physical_instructions=physical))
q='A';s=0;L=6;RR=0
for j,cut in enumerate(trace):
    assert (q+str(s),L,RR)==(cut['control'],cut['L'],cut['R'])
    row=TM[q+str(s)]
    if row is None:assert j==len(trace)-1;break
    w,d,q=row
    if d=='R':RR,s=divmod(RR,2);L=2*L+w
    else:L,s=divmod(L,2);RR=2*RR+w
out={'input':{'raw_A':64,'L':6,'R':0},'tm_steps':len(trace)-1,'virtual_instructions':virtual,
     'physical_instructions':physical,'physical_ADD':adds,'physical_SUB_positive':subpos,'physical_SUB_zero':subzero,
     'correct_membrane_steps':3*physical+subzero,'largest_A_at_virtual_cuts':peak,'tm_cut_trace':trace,
     'method':'Execute literal 3-counter table; use all-input proved prime-macro counts. The enormous two-counter microtrace is not enumerated.'}
assert json.loads((R/'accepting_example.json').read_text())==out
assert (virtual,physical,3*physical+subzero)==(328,738579314485258247,2215737943455775397)
print(json.dumps({'status':'passed','tm_steps':len(trace)-1,'virtual_instructions':virtual,'physical_instructions':physical,'correct_membrane_steps':3*physical+subzero},indent=2))

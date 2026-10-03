#!/usr/bin/env python3
"""Traverse literal serialized rows; never jump or accelerate a macro."""
from verify_pins import verify_inputs
verify_inputs()
from collections import Counter, defaultdict
import hashlib, json
from pathlib import Path
from loader import from_counters, target_ledger
ROOT=Path(__file__).resolve().parent

def require(ok, message):
    if not ok: raise AssertionError(message)
def load(f): return json.loads((ROOT/f).read_text())
def save(f,x): (ROOT/f).write_text(json.dumps(x,indent=2)+'\n')
def grouped(rows):
    d=defaultdict(list)
    for e in rows:d[e['source']].append(e)
    return d
S=load('source.json'); R=load('reversible5.json'); V=load('dependency/virtual3.json')
SG=grouped(S['branches']); RG=grouped(R['rows']); G=target_ledger()
PRIMES=(2,3,5,7,11)
A0=V['tm_cuts']['A0']; B0=V['tm_cuts']['B0']

def run5(q,regs,dest):
    trace=[];v=list(regs);clock=0
    while q!=dest:
        es=[e for e in RG[q] if e['symbol'] not in 'ZP-' or (v[e['counter']]==0 if e['symbol']=='Z' else v[e['counter']]>0)]
        require(len(es)==1, ('five-counter determinism',q,v))
        e=es[0];n=1
        for p,x in zip(PRIMES,v):n*=p**x
        p=PRIMES[e['counter']];x=e['symbol']
        duration=1 if x=='0' else (p+7)*n+3 if x=='+' else 4*n+(p+3)*(n//p)+3 if x=='-' else 4*n+4*(n//p)+3
        trace.append(dict(step=len(trace),control=q,counters=v.copy(),row=e['name'],symbol=x,counter=e['counter'],predicted_literal_duration=duration))
        clock+=duration;v[e['counter']]+={'+':1,'-':-1}.get(x,0);q=e['target']
        require(len(trace)<100000, 'unexpected five-counter budget')
    return dict(control=q,counters=v,steps=len(trace),predicted_literal_steps=clock,trace=trace)

def literal(q,regs,dest,budget=1000000):
    trace=[];v=list(regs);theta=0;counts=Counter();maxima=v.copy()
    while q!=dest:
        enabled=[]
        for b in SG[q]:
            guard=b['guard'];op=guard['op']
            if op=='true' or (v[guard['counter']]==guard['value'] if op=='eq' else v[guard['counter']]>guard['value']): enabled.append(b)
        require(len(enabled)==1, ('serialized determinism',q,v))
        b=enabled[0];i=0 if b['side']==-1 else 1;delta=b['delta']
        micro=1 if delta==0 else 3+2*(G['Z']+v[i])+delta-4*G['S']
        trace.append(dict(step=len(trace),control=q,counters=v.copy(),branch=b['name'],predicted_CA_microedges=micro))
        theta+=micro;counts['zero_update' if delta==0 else 'increment' if delta==1 else 'decrement']+=1
        v[i]+=delta;require(min(v)>=0,'negative counter');q=b['target'];maxima=[max(a,b) for a,b in zip(maxima,v)]
        require(len(trace)<=budget,'literal primitive budget exceeded')
    return dict(control=q,counters=v,steps=len(trace),branch_counts=dict(counts),max_counters=maxima,predicted_CA_microedges=theta,trace=trace)

def formula(a):return 76*a+4*(a//5)+24*(a//7)+48*(a//11)+62
five=run5('START',[0]*5,A0)
freq=Counter((x['symbol'],PRIMES[x['counter']]) for x in five['trace'])
require(freq=={('0',2):5,('Z',5):1,('Z',7):6,('Z',11):12},freq)
require(five['counters']==[0]*5 and five['steps']==24, five)
require(all(x['counters']==[0]*5 for x in five['trace']), 'clean startup changes a counter')
cases=[]
for l,r,c in [(0,0,1),(1,0,1),(0,1,1),(0,0,13),(3,2,1),(1,1,13)]:
    a=from_counters(l,r,0,c)['counter0'];x=literal('START',[a,0],A0)
    require(x['steps']==formula(a) and x['counters']==[a,0], (a,x))
    if a==1:
        save('empty-prologue-literal-trace.json',x)
        require(x['steps']==138 and x['predicted_CA_microedges']==1394018396, 'unexpected empty clock')
    cases.append(dict(input_LRT_cofactor=[l,r,0,c],input_A=a,final_control=x['control'],final_counters=x['counters'],executed_literal_steps=x['steps'],predicted_CA_microedges=x['predicted_CA_microedges'],branch_counts=x['branch_counts']))
save('empty-prologue-five-trace.json',five)
first5=run5(A0,[0]*5,B0)
first2=literal(A0,[1,0],B0,budget=1000000)
require(first5['counters']==[0,0,0,1,0], 'unexpected first TM data/history')
require(first2['counters']==[7,0] and first2['steps']==first5['predicted_literal_steps']==210,'first TM mismatch')
# The dependency's literal four-instruction first TM macro on empty half tapes.
vq=A0;vr=[0,0,0];virtual_steps=0
while vq!=B0:
    op,i,*targets=V['rows'][vq]
    if op=='ADD':vr[i]+=1;vq=targets[0]
    elif vr[i]>0:vr[i]-=1;vq=targets[0]
    else:vq=targets[1]
    virtual_steps+=1
    require(virtual_steps<100, 'unexpected virtual loop')
require(virtual_steps==4 and vr==[0,0,0], 'first TM virtual semantic mismatch')
save('empty-first-tm-five-trace.json',first5);save('empty-first-tm-literal-trace.json',first2)
full=literal('START',[1,0],B0,budget=1000000)
require(full['steps']==348 and full['counters']==[7,0] and full['trace'][138]['control']==A0,'full continuous trace mismatch')
require(full['predicted_CA_microedges']==4182055332,'full CA clock mismatch')
save('empty-through-first-tm-literal-trace.json',full)
receipt=dict(status='PASS',scope='Actual literal serialized-row traversal through initialization and exactly one first TM transition; no macro acceleration, no full universal-program run, no CA execution',source_sha256=hashlib.sha256((ROOT/'source.json').read_bytes()).hexdigest(),all_T_zero_formula='76*A + 4*floor(A/5) + 24*floor(A/7) + 48*floor(A/11) + 62; A=C*2^L*3^R, L,R natural, C positive coprime to 2310',five_counter_prologue_steps=24,cases=cases,first_TM=dict(from_control=A0,to_control=B0,virtual3_steps=virtual_steps,five_counter_steps=first5['steps'],executed_literal_steps=first2['steps'],final_five_counters=first5['counters'],final_two_counters=first2['counters'],predicted_CA_microedges=first2['predicted_CA_microedges'],branch_counts=first2['branch_counts']),empty_total_through_first_TM=dict(executed_literal_steps=138+first2['steps'],predicted_CA_microedges=1394018396+first2['predicted_CA_microedges']),trace_sha256={name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in ('empty-prologue-five-trace.json','empty-prologue-literal-trace.json','empty-first-tm-five-trace.json','empty-first-tm-literal-trace.json','empty-through-first-tm-literal-trace.json')},CA_disclaimer='CA clocks are exact theorem-derived values from the traversed source edges. No CA microedge or raw gate factors were executed or allocated.')
save('initialization-receipt.json',receipt);print(json.dumps(receipt,indent=2))

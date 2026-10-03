from fractions import Fraction as F
from itertools import product
from math import lcm
from pathlib import Path
import json,sys
HERE=Path(__file__).resolve().parent
# Packaged modules are beside this script.
import conservative_signal as cs
import instantiate_morita as im

R={}
# Source table checked visually against independently opened primary rendered page24.
# Independent record of each printed row, including all blank cells.
rows=[
['$-2','$-1','b-11',None,None,None],
['H','Y-1','N-1','*+0','b-1',None],
['*-3','Y-2','N-2','*-2','N',None],
['b+10','1+4','b+5','b+8',None,None],
['Y+6','Y+4','N+4','*+4','$+4',None],
['N+6','Y+5','N+5','*+5','$+5',None],
['b-7',None,None,None,None,None],
['N-3','Y-7','N-7','*-7','$-7','Y-3'],
[None,'Y+8','N+8','*+8','$+9',None],
[None,'Y+9','N+9','*+9','Y+0',None],
[None,'Y+10','N+10','*+10','$-3',None],
['*-12','Y-11','N-11','*-11','$-11',None],
['b+14','Y-12','N-12','b+13',None,None],
['N+0','Y+13','N+13','*+13','$+13',None],
[None,'Y+14','N+14','*+14','$-12',None]]
source={}
for q,row in enumerate(rows):
    for a,item in zip(('b','Y','N','*','$','1'),row):
        if item not in (None,'H','N'):
            source[(f'q{q}',a)]=(item[0],1 if item[1]=='+' else -1,'q'+item[2:])
assert source==im.TM
R['source_visual_transitions_matched']=len(source)

# Independent next-event reference checks all pair intersection times rather
# than only adjacent edges; it then groups positions, uses exact rule sets,
# and sorts each outgoing block.
def reference_event(conf,speeds,rules):
    times=[(y-x)/(speeds[a]-speeds[b]) for i,(x,a) in enumerate(conf)
           for y,b in conf[i+1:] if speeds[a]>speeds[b]]
    if not times:return None
    dt=min(times); assert dt>0
    endpoints=[(x+dt*speeds[a],a) for x,a in conf]
    out=[]; i=0
    while i<len(endpoints):
        j=i+1
        while j<len(endpoints) and endpoints[j][0]==endpoints[i][0]:j+=1
        labels=[a for x,a in endpoints[i:j]]
        if len(labels)>1:labels=sorted(rules[frozenset(labels)],key=lambda a:speeds[a])
        out.extend((endpoints[i][0],a) for a in labels)
        i=j
    return out,dt

def matmul(A,B):
    return [[sum(a*b for a,b in zip(row,col)) for col in zip(*B)] for row in A]

checks=events=ties=triple=zero_starts=0
for n in range(2,6):
    sp={str(i):F(v) for i,v in enumerate((-2,0,2))}
    # transparent exact-set rules for generic simultaneous-event audit
    rules={frozenset(sub):frozenset(sub) for bits in product((0,1),repeat=3)
           if len(sub:=[str(i) for i,b in enumerate(bits) if b])>=2}
    for labels in product(sp,repeat=n):
        for gaps in product((F(0),F(1),F(2)),repeat=n-1):
            if any(g==0 and sp[labels[i]]>=sp[labels[i+1]] for i,g in enumerate(gaps)):continue
            conf=[(F(0),labels[0])]
            for a,g in zip(labels[1:],gaps):conf.append((conf[-1][0]+g,a))
            expected=reference_event(conf,sp,rules)
            actual=cs.event(conf,sp,rules)
            checks+=1;zero_starts+=0 in gaps
            if expected is None:assert actual is None;continue
            out,dt,receipt=actual
            assert (out,dt)==expected
            D=receipt['D'];M=[[D*x for x in row] for row in receipt['A']]
            assert matmul(M,M)==[[D*x for x in row] for row in M]
            events+=1; ties+=len(receipt['J'])>1
            triple+=any(b==a+1 for a,b in zip(receipt['J'],receipt['J'][1:]))
R['generic_event_checks']=dict(cases=checks,events=events,simultaneous_batches=ties,triple_or_larger=triple,zero_gap_initial_germs=zero_starts,all_scaled_projection_identities=True)

# Unlisted simultaneous triple collisions must be rejected, rather than
# decomposed into pair rules or silently completed to identities.
sp={'a':F(2),'b':F(0),'c':F(-2)}
conf=[(F(-1),'a'),(F(0),'b'),(F(1),'c')]
pairs={frozenset(k):frozenset(k) for k in [('a','b'),('b','c'),('a','c')]}
try:cs.event(conf,sp,pairs)
except ValueError:pass
else:raise AssertionError('Omitted triple accepted')
R['undefined_triple_rejected']=True

# Every literal rule independently meets the local normal form.
speeds,rules=im.compile_literal()
assert len(speeds)==114 and len(rules)==445
assert len(set(rules.values()))==len(rules)
assert all(len(a)==len(b)==2 and len({speeds[x] for x in a})==len({speeds[x] for x in b})==2 for a,b in rules.items())
vel=sorted(set(speeds.values()));D=lcm(*(int(abs(a-b)) for a in vel for b in vel if a!=b))
assert D==65520
export=json.loads((HERE.parent/'data'/'MORITA_18_SIGNAL_MACHINE.json').read_text())
assert {k:F(v) for k,v in export['meta_signals'].items()}==speeds
assert {frozenset(r['incoming']):frozenset(r['outgoing']) for r in export['collision_rules']}==rules
R['literal_rules']=dict(meta_signals=len(speeds),collision_rules=len(rules),speeds=list(map(int,vel)),D=D,export_exactly_matched=True)

# Two-half initial loading: unrelated nonblank support on each side; verify
# explicit formula and every first read against an independent base7 sum.
for left in product(range(1,7),repeat=2):
    for right in product(range(1,7),repeat=2):
        tape={-i-1:im.SYMBOLS[v-1] for i,v in enumerate(left)}
        tape.update({i:im.SYMBOLS[v-1] for i,v in enumerate(right)})
        conf=im.initial_signals(tape)
        positions={a:x for x,a in conf}
        def enc(digits):return sum((F(v,7**(i+1)) for i,v in enumerate(digits)),F(1,6*7**len(digits)))
        assert positions['L:mem']+8==enc(left)
        assert 8-positions['R:mem']==enc(right)
R['two_half_loader_cases']=6**4

# Independent synchronous TM tape vs literal signal machine at every source
# read, with an independent event engine and exact cumulative integer lift.
tape,_=im.encode_ctag(('YN','YYN'),'NYY')
conf=im.initial_signals(tape);state='q0';head=0;tm_steps=batches=0
Q=lcm(*(x.denominator for x,a in conf));h=[Q*(conf[i+1][0]-conf[i][0]) for i in range(17)]
scale=Q;halt_seen=None;lift_checks=0
while True:
    expected=reference_event(conf,speeds,rules)
    got=cs.event(conf,speeds,rules)
    if expected is None:assert got is None;break
    new,dt,rec=got;assert (new,dt)==expected
    # Verify the cumulative, not merely reset-per-event, integer orbit.
    M=[[D*x for x in row] for row in rec['A']]
    h=[sum(a*x for a,x in zip(row,h)) for row in M]
    scale*=D
    assert h==[scale*(new[i+1][0]-new[i][0]) for i in range(17)]
    assert all(x.denominator==1 and x>=0 for x in h)
    assert sum(h)==16*scale
    lift_checks+=1
    old_states=[a[2:] for x,a in conf if x==0 and a.startswith('q:q')]
    new_states=[a[2:] for x,a in new if x==0 and a.startswith('q:q')]
    if old_states and old_states!=new_states:
        assert old_states==[state]
        a=tape.get(head,'b')
        token=next(a for x,a in conf if ':vr' in a)
        assert int(token.split('vr')[-1])==im.NUM[a]
        if (state,a) in im.HALT:
            halt_seen=im.HALT[state,a]
            assert any(label==f'h:{state}:{im.NUM[a]}' for x,label in new)
        else:
            b,d,s=source[state,a];tape[head]=b;head+=d;state=s;tm_steps+=1
    conf=new;batches+=1
assert tm_steps==184 and halt_seen=='halt' and batches==11214
R['independent_literal_replay']=dict(tm_steps=tm_steps,event_batches=batches,all_event_batches_matched_independent_engine=True,cumulative_integer_lift_steps=lift_checks,terminal=halt_seen,final_numerator_max_bits=max(int(x).bit_length() for x in h))
print(json.dumps(R,indent=2))
(HERE.parent/'receipts'/'INDEPENDENT_RESULTS.json').write_text(json.dumps(R,indent=2)+'\n')

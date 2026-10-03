from fractions import Fraction as F
from itertools import product
from math import lcm
from pathlib import Path
import sys,json,hashlib
SOURCE=Path(__file__).resolve().parent
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(SOURCE))
import conservative_signal as cs
import instantiate_morita as im

def reference_event(conf,speeds,rules):
    times=[(y-x)/(speeds[a]-speeds[b]) for i,(x,a) in enumerate(conf) for y,b in conf[i+1:] if speeds[a]>speeds[b]]
    if not times:return None
    dt=min(times);assert dt>0
    endpoints=[(x+dt*speeds[a],a) for x,a in conf]
    out=[];i=0
    while i<len(endpoints):
        j=i+1
        while j<len(endpoints) and endpoints[j][0]==endpoints[i][0]:j+=1
        labels=[a for x,a in endpoints[i:j]]
        if len(labels)>1:labels=sorted(rules[frozenset(labels)],key=lambda a:speeds[a])
        out.extend((endpoints[i][0],a) for a in labels);i=j
    return out,dt

def mm(A,B):return [[sum(a*b for a,b in zip(row,col)) for col in zip(*B)] for row in A]

R={'status':'PASS','code_sha256_at_import':{p:hashlib.sha256((SOURCE/p).read_bytes()).hexdigest() for p in ('conservative_signal.py','instantiate_morita.py')}}
cases=events=ties=nonconstant_span=0
for n in range(2,6):
    sp={str(i):F(v) for i,v in enumerate((-2,0,2))}
    rules={frozenset(sub):frozenset(sub) for bits in product((0,1),repeat=3) if len(sub:=[str(i) for i,b in enumerate(bits) if b])>=2}
    for labels in product(sp,repeat=n):
        for gaps in product((F(0),F(1),F(2)),repeat=n-1):
            if any(g==0 and sp[labels[i]]>=sp[labels[i+1]] for i,g in enumerate(gaps)):continue
            conf=[(F(0),labels[0])]
            for a,g in zip(labels[1:],gaps):conf.append((conf[-1][0]+g,a))
            out=cs.event(conf,sp,rules);cases+=1
            if out is None:continue
            new,dt,rec=out;assert (new,dt)==reference_event(conf,sp,rules)
            c=[int(sp[labels[i]]-sp[labels[i+1]]) for i in range(n-1)]
            j=rec['pivot'];s=c[j];assert s>0
            N=[[s*int(i==k)-c[i]*int(k==j) for k in range(n-1)] for i in range(n-1)]
            assert mm(N,N)==[[s*x for x in row] for row in N]
            assert max(abs(x) for row in N for x in row)<=4
            assert sum(x!=0 for row in N for x in row)<=2*(n-2)
            gnew=[new[i+1][0]-new[i][0] for i in range(n-1)]
            hnew=[s*gaps[i]-c[i]*gaps[j] for i in range(n-1)]
            assert hnew==[s*x for x in gnew]
            assert sum(hnew)==s*sum(gaps)-sum(c)*gaps[j]
            nonconstant_span+=sum(c)!=0
            events+=1;ties+=len(rec['J'])>1
R['generic']=dict(cases=cases,events=events,multiple_earliest_edge_batches=ties,generic_nonconstant_span_events=nonconstant_span,projection_identities=True,exact_lift=True)

speed,rules=im.compile_literal();labels_order=sorted(speed);digit={a:i for i,a in enumerate(labels_order)};base=len(digit)
def mode_code(conf):
    q=0
    for x,a in conf:q=base*q+digit[a]
    return q+1

def one_replay(productions,word):
    tape,_=im.encode_ctag(productions,word);conf=im.initial_signals(tape)
    Q=lcm(*(x.denominator for x,a in conf));scale=Q
    h=[int(Q*(conf[i+1][0]-conf[i][0])) for i in range(17)];u=mode_code(conf)*sum(h)
    batches=tm_steps=0;state='q0';head=0;halt=None;pivot_hist={};maxcoef=0;maxs=0;elapsed=F(0);time_num=0
    while True:
        out=cs.event(conf,speed,rules)
        if out is None:assert reference_event(conf,speed,rules) is None;break
        new,dt,rec=out;assert (new,dt)==reference_event(conf,speed,rules)
        v=[int(speed[a]) for x,a in conf];c=[v[i]-v[i+1] for i in range(17)]
        j=rec['pivot'];s=c[j];assert s>0;S=sum(h)
        assert S==16*scale and S>0 and u==mode_code(conf)*S
        assert [F(16*x,S) for x in h]==[conf[i+1][0]-conf[i][0] for i in range(17)]
        assert F(16*h[j],S*s)==dt
        assert sum(c)==0 # Fixed outer stationary marks until the last event.
        hp=[s*h[i]-c[i]*h[j] for i in range(17)]
        oracle_h,oracle_scale=cs.adaptive_lift(h,scale,rec,new,span=16)
        assert oracle_h==hp and oracle_scale==scale*s
        time_num=s*time_num+h[j]
        assert F(16*time_num,sum(hp))==elapsed+dt
        assert sum(hp)==s*S
        assert all(x>=0 for x in hp)
        scale*=s
        assert hp==[scale*(new[i+1][0]-new[i][0]) for i in range(17)]
        assert [F(16*x,sum(hp)) for x in hp]==[new[i+1][0]-new[i][0] for i in range(17)]
        up=mode_code(new)*sum(hp)
        assert up>0
        oldq=[a[2:] for x,a in conf if x==0 and a.startswith('q:q')]
        newq=[a[2:] for x,a in new if x==0 and a.startswith('q:q')]
        if oldq and oldq!=newq:
            assert oldq==[state];symbol=tape.get(head,'b')
            assert any(a.endswith(':vr'+str(im.NUM[symbol])) for x,a in conf)
            if (state,symbol) in im.HALT:halt=im.HALT[state,symbol]
            else:
                b,d,q=im.TM[state,symbol];tape[head]=b;head+=d;state=q;tm_steps+=1
        maxcoef=max(maxcoef,s,max(abs(x) for x in c));maxs=max(maxs,s);pivot_hist[str(s)]=pivot_hist.get(str(s),0)+1
        h,u,conf=hp,up,new;batches+=1;elapsed+=dt
    assert halt is not None and sum(h)==16*scale
    assert max(h)<=16*Q*24**batches
    return dict(productions=list(productions),word=word,tm_steps=tm_steps,event_batches=batches,terminal=halt,pivot_speed_histogram=pivot_hist,max_gap_coefficient_bound=maxcoef,max_pivot_speed=maxs,final_gap_numerator_max_bits=max(h).bit_length(),final_scale_bits=scale.bit_length(),initial_Q_bits=Q.bit_length(),final_mode_coordinate_bits=u.bit_length(),exact_elapsed_time=str(elapsed),state_only_geometry_and_delay_verified=True,cumulative_lift_verified=True,production_helper_verified=True,timed_extension_every_step_verified=True,final_time_numerator_bits=time_num.bit_length())

R['literal_replays']=[one_replay(p,w) for p,w in [(('YN','YYN'),'NYY'),(('YN','YYN'),'Y'),(('YN','YYN'),''),((),'N'),(('',),'NY')]]
assert R['literal_replays'][0]['tm_steps']==184
assert sum(r['event_batches'] for r in R['literal_replays'])==13798
R['literal_total_batches']=13798
(HERE.parent/'receipts'/'PIVOT_SCALE_RESULTS.json').write_text(json.dumps(R,indent=2)+'\n')
print(json.dumps(R,indent=2))

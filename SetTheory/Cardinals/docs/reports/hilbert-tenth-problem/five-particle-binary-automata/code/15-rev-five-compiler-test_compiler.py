import json,random,time
from reversible_binary import compile_source

def fusion(side):
    idx=0 if side==-1 else 1
    zero={'op':'eq','counter':idx,'value':0}
    pos={'op':'gt','counter':idx,'value':0}
    def row(name,source,target,delta,guard):
        return dict(name=name,source=source,target=target,side=side,delta=delta,guard=guard)
    return compile_source(dict(schema='reversible-two-counter-v1',
        controls=['START','ZERO','POS','HALT'],start='START',halt='HALT',class_cut=1,
        branches=[row('test0','START','ZERO',0,zero),row('testp','START','POS',0,pos),
                  row('inc0','ZERO','HALT',1,zero),row('incp','POS','HALT',1,pos)]))

def expected_path(C,start,c0,c1):
    # Return exact unsigned micrograph forward trajectory, with plus signs.
    x=C.encode(start,c0,c1); out=[x]; q=start; cs=[c0,c1]
    while True:
        choices=[e for e in C.branches if e.source==q and e.guard(*cs) and cs[0 if e.side==-1 else 1]+e.delta>=0]
        assert len(choices)<=1
        if not choices: break
        e=choices[0]; v=e.side; idx=0 if v==-1 else 1
        if not e.delta:
            q=e.target; out.append(C.encode(q,*cs)); continue
        markers=[-C.Z-cs[0],0,C.Z+cs[1]]
        def state(mode,anchor): return frozenset(markers+[anchor,anchor+C.gap[(mode,'+')]])
        anchor=v*C.S; out.append(state(('O',e.name),anchor))
        target=markers[0 if v==-1 else 2]-v*C.S
        while anchor!=target:
            anchor+=v;out.append(state(('O',e.name),anchor))
        cs[idx]+=e.delta;markers=[-C.Z-cs[0],0,C.Z+cs[1]]
        anchor=markers[0 if v==-1 else 2]-v*C.S;out.append(state(('I',e.name),anchor))
        target=v*C.S
        while anchor!=target:
            anchor-=v;out.append(state(('I',e.name),anchor))
        q=e.target;out.append(C.encode(q,*cs))
    return out

def flip(C,x):
    close=[(u,v) for u in x for v in x if 0<v-u<=C.D]
    assert len(close)==1
    u,v=close[0]; gap=v-u
    mode,sign=next(k for k,g in C.gap.items() if g==gap)
    return (x-{v})|{u+C.gap[(mode,'-' if sign=='+' else '+')]}

start=time.time(); receipts=[]
for side,c in [(-1,0),(-1,2),(1,0),(1,2)]:
    C=fusion(side); cs=[0,0]; cs[0 if side==-1 else 1]=c
    path=expected_path(C,'START',*cs)
    # All source-boundary, free/contact-boundary, and evenly spaced states;
    # each selected forward edge and inverse is applied by the FULL gate list.
    indices={0,len(path)-2,len(path)-1}
    indices.update(range(0,len(path)-1,47))
    for i,x in enumerate(path[:-1]):
        pair=sorted((u,v) for u in x for v in x if 0<v-u<=C.D)[0]
        anchor=pair[0]; markers=x-set(pair)
        if any(abs(anchor-m) in {C.S,C.S+1,C.L-1,C.L,C.L+1,C.L+2} for m in markers): indices.add(i)
    checked=0
    for i in sorted(indices):
        x=path[i]; want=path[i+1] if i+1<len(path) else flip(C,x)
        got=C.step(x,verify=True)
        assert got==want,(side,c,i,sorted(got),sorted(want))
        assert C.step(got,inverse=True,verify=True)==x
        if i>0:
            rev=C.step(flip(C,x),verify=True)
            assert rev==flip(C,path[i-1]),(side,c,i,'reverse')
        checked+=1
    assert C.step(flip(C,path[0]),verify=True)==path[0]
    receipts.append(dict(side=side,counter=c,forward_microedges=len(path)-1,selected_full_steps=checked,ledger=C.ledger()))
    print('passed',side,c,len(path)-1,checked,flush=True)
# Full-factor malformed finite-input reversibility checks, including nearby heads.
C=fusion(-1); rng=random.Random(20261003)
for trial in range(40):
    x=frozenset(rng.sample(range(-120,121),rng.randrange(0,15)))
    y=C.step(x,verify=True)
    assert len(x)==len(y) and C.step(y,inverse=True,verify=True)==x
print(json.dumps(dict(status='passed',runs=receipts,malformed_random=40,seconds=time.time()-start),indent=2))
open('test-receipt.json','w').write(json.dumps(dict(status='passed',runs=receipts,malformed_random=40,seconds=time.time()-start),indent=2)+'\n')

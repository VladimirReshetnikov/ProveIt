import json
from reversible_binary import compile_source
C=compile_source(json.load(open('sample-source.json')))
x=C.encode(C.start,0,0);initial=x;rows=[];hits=[]
word={0,C.S,C.S+C.gap[(('H',C.halt),'+')]}
period=2*(3+2*C.Z+1-4*C.S)+2
boundary=[]
for t in range(period):
    close=[(u,v) for u in x for v in x if 0<v-u<=C.D];assert len(close)==1
    anchor,end=close[0]
    mode,sign=next(k for k,d in C.gap.items() if d==end-anchor)
    hit={z for z in x if 0<=z<=C.S+C.D}==word
    if hit:hits.append(t)
    rows.append(dict(t=t,ones=sorted(x),mode=list(mode),phase=sign,halt_observer=hit))
    if sign=='+' and mode[0]=='O' and anchor in (-C.L,-C.L-1,-C.Z+C.L+1,-C.Z+C.L):
        mid=x;active=[]
        for g in C.E:
            y=g.apply(mid,True)
            if y!=mid:active.append(g.name)
            mid=y
        inverse_active=[g.name for g in C.E if g.apply(mid)!=mid]
        assert len(active)==len(inverse_active)==1 and active==inverse_active
        boundary.append(dict(t=t,input_ones=sorted(x),input_anchor=anchor,edge_gate=active[0],after_E_ones=sorted(mid),reverse_edge_gate=inverse_active[0]))
    x=C.step(x)
assert x==initial and len({tuple(r['ones']) for r in rows})==period
assert hits==[(period-2)//2]
json.dump(dict(source_file='sample-source.json',input_counters=[0,0],ledger=C.ledger(),first_halt=hits[0],reflection_period=period,observer_hits=hits,states=rows),open('sample-orbit.json','w'),indent=2)
json.dump(boundary,open('sample-boundary-demonstration.json','w'),indent=2)
json.dump(dict(status='passed',ledger=C.ledger(),initial_ones=sorted(initial),halt_ones=rows[hits[0]]['ones'],first_halt=hits[0],reflection_period=period,boundary_tests=len(boundary)),open('sample-receipt.json','w'),indent=2)
print(open('sample-receipt.json').read())

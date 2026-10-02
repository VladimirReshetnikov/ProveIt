"""Linear-size event/adjacency-lifetime quadratic compiler. See the accompanying article."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json, random
from signal_geometry import speed_modulus, output, trace, next_layer, lin, polynomial, linear_rank


def plus(a,b,k=1):
    z=dict(a)
    for v,c in b.items(): z[v]=z.get(v,0)+k*c
    return {v:c for v,c in z.items() if c}


def compile_sparse(machine, initial_labels, schema, halt=False):
    speeds,_=machine; assert all(type(v) is int and v>=0 for v in speeds.values())
    K=len(schema);B=speed_modulus(speeds)**K
    rows=[];variables=[];segments={};events=[];lifetimes=[]
    def var(name): variables.append(name);return name
    def require(expr,strict,name):
        if strict:
            s=var(name);expr=plus(expr,{s:-1,'@':-1})
        rows.append(expr)
    def t(i): return {} if i==0 else {f't{i}':1}
    def at(s,i):
        z=segments[s];return plus(plus(z['p'],t(i),z['v']),t(z['born']),-z['v'])
    def gap(pair,i): return plus(at(pair[1],i),at(pair[0],i),-1)
    live=[]
    for j,label in enumerate(initial_labels):
        key=f'initial{j}';live.append(key)
        segments[key]=dict(label=label,v=speeds[label],p={f'x{j}':B},born=0,event=None,death=None)
    for j in range(len(live)-1):
        require({f'x{j+1}':1,f'x{j}':-1},True,f'input_gap{j}')
    active={pair:0 for pair in zip(live,live[1:])}
    def finish(pair,start,end):
        assert start<end
        a,b=(segments[s] for s in pair)
        lower_equal=a['event'] is not None and a['event']==b['event'] and a['born']==start
        upper_equal=a['death'] is not None and a['death']==b['death']
        if lower_equal: assert a['v']<b['v']
        idx=len(lifetimes)
        require(gap(pair,start),not lower_equal,f'lower{idx}')
        require(gap(pair,end),not upper_equal,f'upper{idx}')
        lifetimes.append(dict(pair=pair,start=start,end=end,lower_equal=lower_equal,upper_equal=upper_equal))
    for i,blocks in enumerate(schema,1):
        var(f't{i}');var(f'd{i}')
        rows.append(plus(plus(t(i),t(i-1),-1),{f'd{i}':-1,'@':-1}))
        assert [j for b in blocks for j in b] == list(range(len(live)))
        assert all(blocks) and any(len(b)>=2 for b in blocks)
        new=[]
        for bi,block in enumerate(blocks):
            inc=[live[j] for j in block]
            if len(inc)==1: new.extend(inc);continue
            vv=[segments[s]['v'] for s in inc]
            assert all(a>b for a,b in zip(vv,vv[1:]))
            e=len(events);x=var(f'e{e}')
            out=output(machine,[segments[s]['label'] for s in inc])
            events.append(dict(batch=i,block=bi,position=x,incoming=inc,outgoing=out))
            for s in inc:
                rows.append(plus({x:1},at(s,i),-1));segments[s]['death']=e
            for j,label in enumerate(out):
                s=f'event{e}_{j}';new.append(s)
                segments[s]=dict(label=label,v=speeds[label],p={x:1},born=i,event=e,death=None)
        newpairs=set(zip(new,new[1:]));oldpairs=set(active)
        for pair in sorted(oldpairs-newpairs): finish(pair,active.pop(pair),i)
        for pair in sorted(newpairs-oldpairs): active[pair]=i
        live=new
    if halt:
        for pair,start in sorted(active.items()):
            a,b=(segments[s] for s in pair);assert a['v']<=b['v']
            lower_equal=a['event'] is not None and a['event']==b['event'] and a['born']==start
            if lower_equal: assert a['v']<b['v']
            idx=len(lifetimes)
            require(gap(pair,start),not lower_equal,f'lower{idx}')
            lifetimes.append(dict(pair=pair,start=start,end=None,lower_equal=lower_equal,upper_equal=False))
    else:
        for pair,start in sorted(active.items()):
            if start<K: finish(pair,start,K)
    A=len(lifetimes);E=len(events);I=sum(len(e['incoming']) for e in events)
    n=len(initial_labels);Lbound=max(0,n-1)+sum(len(e['outgoing'])+1 for e in events)
    assert A<=Lbound
    assert len(variables)<=E+2*K+2*A+max(0,n-1)
    assert len(rows)<=I+K+2*A+max(0,n-1)
    return dict(B=B,D=speed_modulus(speeds),variables=variables,rows=rows,segments=segments,
                events=events,lifetimes=lifetimes,final_live=live,halt=halt,K=K,
                counts=dict(events=E,incoming=I,lifetimes=A,lifetime_bound=Lbound,
                            witnesses=len(variables),residuals=len(rows)))


def sparse_witness(cert,positions,layers):
    a={f'x{j}':x for j,x in enumerate(positions)};B=cert['B'];time=F(0)
    for i,z in enumerate(layers,1):
        time+=z['dt'];a[f't{i}']=B*time;a[f'd{i}']=B*z['dt']-1
    for e in cert['events']:
        z=layers[e['batch']-1];a[e['position']]=B*z['end'][z['blocks'][e['block']][0]]
    # Every remaining variable is a gap slack, whose unique coefficient is -1.
    for row in cert['rows']:
        unknown=[k for k in row if k!='@' and k not in a]
        if unknown:
            assert len(unknown)==1 and row[unknown[0]]==-1
            a[unknown[0]]=sum(c*(1 if k=='@' else a[k]) for k,c in row.items() if k!=unknown[0])
    assert set(a)==set(cert['variables'])|{f'x{j}' for j in range(len(positions))}
    assert all(F(x).denominator==1 and x>=0 for x in a.values())
    return {k:int(v) for k,v in a.items()}


def check():
    rng=random.Random(2026100201);speeds={'a':0,'b':2,'c':3,'d':4}
    subsets=[s for bits in product((0,1),repeat=4) if sum(bits)>=2 for s in [tuple(x for x,b in zip(speeds,bits) if b)]]
    fixtures=[((speeds,{}),list('dba'),[0,1,2],6),
              ((speeds,{frozenset('da'):()}),list('dada'),[0,4,8,12],3),
              ((speeds,{frozenset('da'):('b','c')}),list('dad'),[0,4,10],6),
              ((speeds,{}),list('dba'),[0,2,4],1),
              ((speeds,{}),[],[],0),((speeds,{}),['a'],[0],0)]
    for _ in range(240):
        rules={frozenset(s):tuple(rng.sample(list(speeds),rng.randrange(5))) for s in subsets}
        labels=[rng.choice(list(speeds)) for _ in range(rng.randrange(2,9))]
        pos=[];p=0
        for label in labels:p+=rng.randrange(1,6);pos.append(p)
        fixtures.append(((speeds,rules),labels,pos,8))
    counts=dict(certificates=0,layers=0,events=0,lifetimes=0,coordinate_mutations=0,
                rank_checks=0,terminal_ray_certificates=0,one_layer_candidates=0,
                missed_final_collision_regressions=0,height_checks=0)
    examples=[]
    for machine,labels,pos,K in fixtures:
        layers=trace(machine,labels,pos,K);schema=[z['blocks'] for z in layers]
        final_labels=layers[-1]['labels'] if layers else labels
        halted=all(speeds[a]<=speeds[b] for a,b in zip(final_labels,final_labels[1:]))
        for halt in [False]+([True] if halted else []):
            c=compile_sparse(machine,labels,schema,halt=halt);a=sparse_witness(c,pos,layers)
            assert polynomial(c,a)==0
            counts['certificates']+=1;counts['layers']+=len(layers)
            counts['events']+=c['counts']['events'];counts['lifetimes']+=c['counts']['lifetimes']
            counts['terminal_ray_certificates']+=int(halt)
            for v in c['variables']:
                bad=dict(a);bad[v]+=1;assert polynomial(c,bad)>0
                counts['coordinate_mutations']+=1
            if counts['rank_checks']<40:
                assert linear_rank(c)==len(c['variables']);counts['rank_checks']+=1
            M=max([1]+pos);bound=2*60**len(layers)*M
            assert max([0]+list(a.values()))<=bound;counts['height_checks']+=1
            if len(examples)<5: examples.append(dict(certificate=c,assignment=a))
    # All three-signal one-layer schedules, valid and invalid.
    for labels in product(speeds,repeat=3):
        for g1,g2 in product(range(1,5),repeat=2):
            pos=[0,g1,g1+g2];actual=next_layer((speeds,{}),list(labels),list(map(F,pos)))
            for blocks in [[[0,1],[2]],[[0],[1,2]],[[0,1,2]]]:
                try:c=compile_sparse((speeds,{}),labels,[blocks])
                except AssertionError:continue
                b=next(b for b in blocks if len(b)>1);j,k=b[:2]
                dt=F(pos[k]-pos[j],speeds[labels[j]]-speeds[labels[k]])
                z=dict(dt=dt,end=[p+speeds[x]*dt for p,x in zip(pos,labels)],blocks=blocks)
                try:a=sparse_witness(c,pos,[z]);accepted=polynomial(c,a)==0
                except AssertionError:accepted=False
                assert accepted==(actual is not None and actual['blocks']==blocks)
                counts['one_layer_candidates']+=1
    # A distant omitted collision exactly at final time must fail.
    machine=(speeds,{frozenset('da'):()});labels=list('dada');pos=[0,4,10,14]
    c=compile_sparse(machine,labels,[[[0,1],[2],[3]]])
    fake=[dict(dt=F(1),end=list(map(F,[4,4,14,14])),blocks=[[0,1],[2],[3]])]
    try:a=sparse_witness(c,pos,fake);accepted=polynomial(c,a)==0
    except AssertionError:accepted=False
    assert not accepted;counts['missed_final_collision_regressions']+=1
    Path(__file__).with_name('signal_sparse_examples.json').write_text(json.dumps(examples,indent=2)+'\n')
    Path(__file__).with_name('signal_sparse_receipt.json').write_text(json.dumps(counts,indent=2)+'\n')
    print(json.dumps(counts,indent=2))


if __name__=='__main__':check()

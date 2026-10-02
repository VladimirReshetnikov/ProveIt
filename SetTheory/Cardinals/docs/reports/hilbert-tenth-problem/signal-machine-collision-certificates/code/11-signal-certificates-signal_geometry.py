"""Direct convex-quadratic certificates for fixed rational signal schemas.

Pure Python exact arithmetic. No solver, floating point, or MRDP oracle.
Coordinates are natural numbers. Speeds are nonnegative integers.
Blank collisions must be explicit in the machine semantics (default identity).
"""
from fractions import Fraction as F
from itertools import combinations, product
from math import lcm
import json, random
from pathlib import Path


def speed_modulus(speeds):
    return lcm(1, *(abs(a-b) for a in speeds.values() for b in speeds.values() if a != b))


def output(machine, labels):
    speeds, rules = machine
    assert len(set(speeds[x] for x in labels)) == len(labels)
    out = rules.get(frozenset(labels), tuple(labels))
    assert len(set(out)) == len(out)
    assert len(set(speeds[x] for x in out)) == len(out)
    return sorted(out, key=speeds.get)


def next_layer(machine, labels, positions):
    """Independent event-driven rational semantics, all simultaneous events."""
    speeds, _ = machine
    candidates = [F(positions[j+1]-positions[j], speeds[labels[j]]-speeds[labels[j+1]])
                  for j in range(len(labels)-1)
                  if speeds[labels[j]] > speeds[labels[j+1]]]
    if not candidates:
        return None
    assert all(t > 0 for t in candidates)
    dt = min(candidates)
    end = [p + speeds[x]*dt for x,p in zip(labels,positions)]
    assert all(a <= b for a,b in zip(end,end[1:]))
    blocks=[]
    for j,p in enumerate(end):
        if j and p == end[j-1]: blocks[-1].append(j)
        else: blocks.append([j])
    out_labels=[]; out_positions=[]
    for block in blocks:
        out = [labels[block[0]]] if len(block)==1 else output(machine,[labels[j] for j in block])
        out_labels.extend(out); out_positions.extend([end[block[0]]]*len(out))
    return dict(dt=dt, end=end, blocks=blocks, labels=out_labels, positions=out_positions)


def trace(machine, labels, positions, limit):
    labels=list(labels); positions=list(map(F,positions)); result=[]
    for _ in range(limit):
        layer=next_layer(machine,labels,positions)
        if layer is None: break
        result.append(layer); labels,positions=layer['labels'],layer['positions']
    return result


def lin(*pairs):
    d={}
    for k,c in pairs:
        d[k]=d.get(k,0)+c
    return {k:c for k,c in d.items() if c}


def compile_schema(machine, initial_labels, blocks_by_layer, halt=False):
    """Rows are integer affine dictionaries; '@' is their constant term.

    Inputs x0,... are ordered nonnegative integer initial positions.
    Every collision group is retained in boundary order, even if it erases.
    """
    speeds,_=machine
    assert all(type(v) is int and v>=0 for v in speeds.values())
    K=len(blocks_by_layer); B=speed_modulus(speeds)**K
    labels=list(initial_labels)
    starts=[(f'x{j}',B) for j in range(len(labels))]
    rows=[]; variables=[]; sizes=[]
    for j in range(len(labels)-1):
        s=f'initial_gap_{j}'; variables.append(s)
        rows.append(lin((f'x{j+1}',1),(f'x{j}',-1),(s,-1),('@',-1)))
    for i,blocks in enumerate(blocks_by_layer):
        n=len(labels); g=len(blocks)
        assert [j for block in blocks for j in block] == list(range(n))
        assert all(block for block in blocks) and any(len(b)>=2 for b in blocks)
        sizes.append((n,g)); d=f'd{i}'; variables.append(d)
        ends=[f'c{i}_{j}' for j in range(n)]; variables.extend(ends)
        for j,(name,coef) in enumerate(starts):
            v=speeds[labels[j]]
            rows.append(lin((ends[j],1),(name,-coef),(d,-v),('@',-v)))
        new_labels=[]; new_starts=[]
        for k,block in enumerate(blocks):
            if len(block)>1:
                vv=[speeds[labels[j]] for j in block]
                assert all(a>b for a,b in zip(vv,vv[1:]))
                out=output(machine,[labels[j] for j in block])
                for j in block[1:]: rows.append(lin((ends[j],1),(ends[block[0]],-1)))
            else: out=[labels[block[0]]]
            if k:
                s=f'gap_{i}_{k}';variables.append(s)
                rows.append(lin((ends[block[0]],1),(ends[blocks[k-1][0]],-1),(s,-1),('@',-1)))
            new_labels.extend(out);new_starts.extend([(ends[block[0]],1)]*len(out))
        labels,starts=new_labels,new_starts
    if halt:
        assert all(speeds[a]<=speeds[b] for a,b in zip(labels,labels[1:]))
    assert len(variables) == max(0,len(initial_labels)-1)+sum(n+g for n,g in sizes)
    assert len(rows) == max(0,len(initial_labels)-1)+sum(2*n-1 for n,g in sizes)
    return dict(B=B,D=speed_modulus(speeds),variables=variables,rows=rows,sizes=sizes,
                initial_labels=list(initial_labels),final_labels=labels,halt=halt)


def witness(cert, initial_positions, layers):
    B=cert['B']; a={f'x{j}':x for j,x in enumerate(initial_positions)}
    for j in range(len(initial_positions)-1): a[f'initial_gap_{j}']=initial_positions[j+1]-initial_positions[j]-1
    for i,layer in enumerate(layers):
        a[f'd{i}']=B*layer['dt']-1
        for j,x in enumerate(layer['end']): a[f'c{i}_{j}']=B*x
        for k in range(1,len(layer['blocks'])):
            a[f'gap_{i}_{k}']=B*(layer['end'][layer['blocks'][k][0]]-layer['end'][layer['blocks'][k-1][0]])-1
    assert all(F(x).denominator==1 and x>=0 for x in a.values())
    return {k:int(x) for k,x in a.items()}


def polynomial(cert, assignment):
    assert all(type(v) is int and v>=0 for v in assignment.values())
    return sum(sum(c*(1 if k=='@' else assignment[k]) for k,c in row.items())**2 for row in cert['rows'])


def linear_rank(cert):
    A=[[F(row.get(v,0)) for v in cert['variables']] for row in cert['rows']]
    r=0
    for c in range(len(cert['variables'])):
        k=next((i for i in range(r,len(A)) if A[i][c]),None)
        if k is None: continue
        A[r],A[k]=A[k],A[r]; pivot=A[r][c]; A[r]=[x/pivot for x in A[r]]
        for i in range(r+1,len(A)):
            if A[i][c]:
                m=A[i][c]; A[i]=[x-m*y for x,y in zip(A[i],A[r])]
        r+=1
    return r


def check():
    rng=random.Random(20261002)
    counts=dict(certificates=0,layers=0,coordinate_mutations=0,rank_checks=0,
                small_exhaustive_assignments=0,one_layer_candidates=0)
    speeds={'a':0,'b':2,'c':3,'d':4}
    allsets=[s for k in range(2,5) for s in combinations(speeds,k)]
    examples=[]
    fixtures=[
        ((speeds,{}),list('dba'),[0,1,2],4),
        ((speeds,{frozenset('da'):()}),list('dada'),[0,4,8,12],2),
        ((speeds,{frozenset('da'):('b','c')}),list('dad'),[0,4,10],5),
        ((speeds,{}),list('dba'),[0,2,4],1),
    ]
    for _ in range(160):
        rules={frozenset(s):tuple(rng.sample(list(speeds),rng.randrange(5))) for s in allsets}
        labels=[rng.choice(list(speeds)) for _ in range(rng.randrange(2,7))]
        pos=[];p=0
        for x in labels: p+=rng.randrange(1,5);pos.append(p)
        fixtures.append(((speeds,rules),labels,pos,6))
    for machine,labels,pos,K in fixtures:
        layers=trace(machine,labels,pos,K)
        if not layers: continue
        cert=compile_schema(machine,labels,[z['blocks'] for z in layers])
        a=witness(cert,pos,layers); assert polynomial(cert,a)==0
        counts['certificates']+=1;counts['layers']+=len(layers)
        for v in cert['variables']:
            b=dict(a);b[v]+=1;assert polynomial(cert,b)>0;counts['coordinate_mutations']+=1
        if counts['rank_checks']<30:
            assert linear_rank(cert)==len(cert['variables']);counts['rank_checks']+=1
        if len(examples)<4:
            examples.append(dict(certificate=cert,assignment=a,layer_durations=[str(z['dt']) for z in layers]))
    # Exhaust all small natural tuples for a two-signal collision, including input order slack.
    machine=({'r':2,'s':0},{})
    cert=compile_schema(machine,['r','s'],[[[0,1]]],halt=True)
    zeros=[]
    for vals in product(range(5),repeat=len(cert['variables'])):
        a={'x0':0,'x1':1,**dict(zip(cert['variables'],vals))}
        if polynomial(cert,a)==0: zeros.append(vals)
        counts['small_exhaustive_assignments']+=1
    assert len(zeros)==1
    # Every possible one-layer partition for three input signals, including wrong schedules.
    parts=[[[0,1],[2]],[[0],[1,2]],[[0,1,2]]]
    for labels in product(speeds,repeat=3):
        for g1,g2 in product(range(1,5),repeat=2):
            pos=[0,g1,g1+g2]; actual=next_layer((speeds,{}),list(labels),list(map(F,pos)))
            for blocks in parts:
                try: c=compile_schema((speeds,{}),labels,[blocks])
                except AssertionError: continue
                block=next(b for b in blocks if len(b)>1);j,k=block[:2]
                dt=F(pos[k]-pos[j],speeds[labels[j]]-speeds[labels[k]])
                end=[p+speeds[x]*dt for p,x in zip(pos,labels)]
                layer={'dt':dt,'end':end,'blocks':blocks}
                try: a=witness(c,pos,[layer]); accepted=polynomial(c,a)==0
                except AssertionError: accepted=False
                expected=actual is not None and actual['blocks']==blocks
                assert accepted==expected,(labels,pos,blocks,accepted,expected)
                counts['one_layer_candidates']+=1
    Path(__file__).with_name('signal_geometry_examples.json').write_text(json.dumps(examples,indent=2)+'\n')
    Path(__file__).with_name('signal_geometry_receipt.json').write_text(json.dumps(counts,indent=2)+'\n')
    print(json.dumps(counts,indent=2))


if __name__=='__main__': check()

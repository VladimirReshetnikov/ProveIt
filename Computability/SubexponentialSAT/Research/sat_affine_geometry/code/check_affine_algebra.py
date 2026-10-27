#!/usr/bin/env python3
"""Independent exact graphical-sum checks for the new contraction menus.

The coefficient ring is (Z/64Z)[V]/(V^2). Each directed pair is an independent
index, with dimension zero, one or two in these small fixtures. The tested
algorithm caches every group function exactly once per incident assignment,
builds all planned subset tables, and performs the final triangle by literal
rectangular matrix multiplication and a trace. It implements no fast matrix
backend and makes no SAT runtime claim. No upstream code is imported.
"""
from dataclasses import dataclass
from itertools import product
from math import prod
from pathlib import Path
import argparse
import json

MOD=64
ZERO=(0,0)
ONE=(1,0)


def require(condition,message):
    if not condition:
        raise ValueError(message)


def add(a,b):
    return ((a[0]+b[0])%MOD,(a[1]+b[1])%MOD)


def mul(a,b):
    return (a[0]*b[0]%MOD,(a[0]*b[1]+a[1]*b[0])%MOD)


def plans_for(r):
    if r==4:
        return [[[0,1],[2],[3]]]
    if r in (7,8,9):
        plans=[]
        for direction in range(4):
            blocks=[]
            for intercept in range(3):
                blocks.append([3*x+y for x,y in product(range(3),repeat=2)
                               if 3*x+y<r and
                               (x if direction==3 else (y-direction*x)%3)
                               ==intercept])
            plans.append(blocks)
        return plans
    if r==12:
        return [
            [[0,1,2,3],[4,5,6,7],[8,9,10,11]],
            [[9,6,4,0],[1,7,10,11],[5,3,2,8]],
            [[1,2,10,4],[3,11,6,9],[7,0,8,5]],
            [[0,5,10,11],[3,8,1,6],[4,9,7,2]],
        ]
    raise ValueError('Unsupported group count')


def assignments(edges,dimensions):
    for values in product(*(range(dimensions[e]) for e in edges)):
        yield dict(zip(edges,values))


def group_value(v,r,assignment,seed,variant):
    """A deterministic test oracle, with directed indices kept distinct."""
    if variant=='one':
        return ONE
    inc=[(i,j) for i in range(r) for j in range(r) if i!=j and v in (i,j)]
    base=17*seed+11*(v+1)
    linear=7*seed+19*(v+1)
    for k,e in enumerate(inc):
        x=assignment.get(e,0)
        base+=(7*(e[0]+1)+13*(e[1]+1))*(x+1)
        linear+=(k+3)*(x+1)*(x+2)
    # Nonseparable dependence on two incident indices helps detect lost ports.
    for left,right in zip(inc,inc[1:]):
        base+=3*assignment.get(left,0)*assignment.get(right,0)
        linear+=5*assignment.get(left,0)*assignment.get(right,0)
    a=2*(base%32)+1
    b=linear%64
    if variant=='mixed' and v in (0,r-1):
        a=base%64
    elif variant=='even' and v==0:
        a=2*(1+base%16)
    elif variant=='nilpotent' and v==0:
        a=0;b=2*(linear%32)+1
    elif variant=='double_nilpotent' and v in (0,1):
        a=0;b=2*(linear%32)+1
    return (a%64,b%64)


def literal_sum(r,dimensions,seed,variant):
    """Independent oracle: direct polynomial coefficient formula, no mul()."""
    if any(d==0 for d in dimensions.values()):
        return ZERO
    active=tuple(e for e,d in dimensions.items() if d>1)
    constant=0;linear=0
    for assignment in assignments(active,dimensions):
        vals=[group_value(v,r,assignment,seed,variant) for v in range(r)]
        constant+=prod(a for a,b in vals)
        linear+=sum(vals[v][1]*prod(vals[j][0] for j in range(r) if j!=v)
                    for v in range(r))
    return (constant%64,linear%64)


@dataclass
class Table:
    vertices:frozenset
    boundary:tuple
    data:dict


def planned_sum(r,dimensions,seed,variant,blocks):
    require(len(blocks)==3 and all(blocks),'Three nonempty blocks required')
    require(sorted(sum(blocks,[]))==list(range(r)),'Blocks do not partition groups')
    require(all(type(d) is int and d>=0 for d in dimensions.values()),
            'Invalid index dimension')
    if any(d==0 for d in dimensions.values()):
        return ZERO,{'group_entry_calls':0,'per_group_calls':[0]*r,
                     'expected_calls':0,'binary_merges':0,'triangle_products':0,
                     'maximum_table_entries':0,'empty_allocation_skipped':True}
    active=tuple(e for e,d in dimensions.items() if d>1)
    call_counts=[0]*r
    caches={}
    peak=0
    for v in range(r):
        boundary=tuple(e for e in active if v in e)
        data={}
        for a in assignments(boundary,dimensions):
            key=tuple(a[e] for e in boundary)
            data[key]=group_value(v,r,a,seed,variant)
            call_counts[v]+=1
        expected=prod(dimensions[e] for e in dimensions if v in e)
        require(call_counts[v]==expected,'Singleton cache made wrong number of oracle calls')
        caches[v]=Table(frozenset([v]),boundary,data)
        peak=max(peak,len(data))
    merges=0
    def merge(a,b):
        nonlocal merges,peak
        require(not (a.vertices&b.vertices),'Overlapping merged subsets')
        internal=tuple(sorted(set(a.boundary)&set(b.boundary)))
        exterior=tuple(sorted(set(a.boundary)^set(b.boundary)))
        data={}
        for x in assignments(exterior,dimensions):
            value=ZERO
            for z in assignments(internal,dimensions):
                combined=x|z
                av=a.data[tuple(combined[e] for e in a.boundary)]
                bv=b.data[tuple(combined[e] for e in b.boundary)]
                value=add(value,mul(av,bv))
            data[tuple(x[e] for e in exterior)]=value
        merges+=1;peak=max(peak,len(data))
        return Table(a.vertices|b.vertices,exterior,data)
    def build(block):
        if len(block)==1:
            return caches[block[0]]
        split=len(block)//2
        return merge(build(block[:split]),build(block[split:]))
    a,b,c=[build(block) for block in blocks]
    ab=tuple(sorted(set(a.boundary)&set(b.boundary)))
    ac=tuple(sorted(set(a.boundary)&set(c.boundary)))
    bc=tuple(sorted(set(b.boundary)&set(c.boundary)))
    require(set(a.boundary)==set(ab)|set(ac),'Wrong first triangle ports')
    require(set(b.boundary)==set(ab)|set(bc),'Wrong second triangle ports')
    require(set(c.boundary)==set(ac)|set(bc),'Wrong third triangle ports')
    require(not(set(ab)&set(ac) or set(ab)&set(bc) or set(ac)&set(bc)),
            'Triangle index classes overlap')
    result=ZERO;products=0
    # Contract A^T B, whose rows are AC and columns BC, then pair with C.
    for x in assignments(ac,dimensions):
        for y in assignments(bc,dimensions):
            exterior=x|y
            entry=ZERO
            for z in assignments(ab,dimensions):
                assignment=exterior|z
                av=a.data[tuple(assignment[e] for e in a.boundary)]
                bv=b.data[tuple(assignment[e] for e in b.boundary)]
                entry=add(entry,mul(av,bv));products+=1
            cv=c.data[tuple(exterior[e] for e in c.boundary)]
            result=add(result,mul(entry,cv));products+=1
    expected=sum(prod(dimensions[e] for e in dimensions if v in e) for v in range(r))
    require(sum(call_counts)==expected,'Unpaid or missing group-entry calls')
    require(merges==r-3,'Wrong number of internal matrix operations')
    return result,{'group_entry_calls':sum(call_counts),'per_group_calls':call_counts,
                   'expected_calls':expected,'binary_merges':merges,
                   'triangle_products':products,'maximum_table_entries':peak,
                   'empty_allocation_skipped':False}


def fixtures(r):
    cycle=[(i,(i+1)%r) for i in range(min(r,5))]
    sparse=list(dict.fromkeys(cycle+[(1,0)]))[:5]
    bidirectional=[(0,1),(1,0),(0,2),(2,0)]
    disconnected=[(0,1),(1,0),(r-2,r-1),(r-1,r-2)]
    specifications=[
        ('all_unit_dimensions',[],'generic',False),
        ('sparse_directed','SPARSE','generic',False),
        ('orientation_ports',bidirectional,'mixed',False),
        ('even_zero_divisor',cycle,'even',False),
        ('one_nilpotent',bidirectional[:3],'nilpotent',False),
        ('nilpotent_annihilation',bidirectional,'double_nilpotent',False),
        ('disconnected_pairs',disconnected,'mixed',False),
        ('counting_identity',sparse,'one',False),
        ('empty_index_list',sparse,'generic',True),
    ]
    for i,(name,edges,variant,empty) in enumerate(specifications):
        if edges=='SPARSE':edges=sparse
        dims={(u,v):1 for u in range(r) for v in range(r) if u!=v}
        for e in edges:dims[e]=2
        if empty:dims[0,1]=0
        yield name,dims,variant,103+11*r+i


def certificate():
    require(mul((0,1),(0,1))==ZERO,'V is not nilpotent in the implementation')
    require(mul((2,0),(32,0))==ZERO,'Expected scalar zero divisors missing')
    require(mul((1,1),(1,63))==ONE,'Truncated polynomial product is wrong')
    rows=[];total_plans=0;total_calls=0;total_literal_assignments=0
    for r in [4,7,8,9,12]:
        menus=plans_for(r)
        for name,dims,variant,seed in fixtures(r):
            expected=literal_sum(r,dims,seed,variant)
            naive_assignments=prod(dims.values())
            total_literal_assignments+=naive_assignments
            if variant=='one':require(expected==(naive_assignments%64,0),
                                     'Counting identity failed')
            if variant=='double_nilpotent':require(expected==ZERO,
                                                  'Nilpotent annihilation failed')
            outcomes=[]
            for j,blocks in enumerate(menus):
                result,counts=planned_sum(r,dims,seed,variant,blocks)
                require(result==expected,f'Graphical sum mismatch: r={r},fixture={name},plan={j}')
                total_plans+=1;total_calls+=counts['group_entry_calls']
                outcomes.append({'plan':j,'result':list(result),**counts})
            rows.append({'groups':r,'fixture':name,'variant':variant,
                         'nontrivial_directed_dimensions':[[u,v,d] for (u,v),d in dims.items() if d!=1],
                         'literal_assignment_count':naive_assignments,
                         'literal_result':list(expected),'plans':outcomes})
    # Bad dimensions must be rejected before any contraction is attempted.
    bad={(u,v):1 for u in range(4) for v in range(4) if u!=v};bad[0,1]=-1
    rejected=False
    try:planned_sum(4,bad,1,'generic',plans_for(4)[0])
    except ValueError:rejected=True
    require(rejected,'Negative dimension control was accepted')
    return {'status':'PASS','ring':'(Z/64Z)[V]/(V^2)',
            'group_counts':[4,7,8,9,12], 'fixtures':len(rows),
            'planned_contractions_checked':total_plans,
            'literal_assignments_checked':total_literal_assignments,
            'paid_group_entry_calls':total_calls,
            'oracle':'Direct coefficient formula for product of degree-one factors; no shared multiplication routine',
            'backend':'Literal finite rectangular matrix products; no fast matrix multiplication implementation',
            'empty_list_rule':'Any zero dimension skips the entire allocation before all group-entry calls',
            'negative_dimension_control':'REJECTED','cases':rows}


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path)
    args=p.parse_args()
    text=json.dumps(certificate(),indent=2,sort_keys=True)+'\n'
    if args.output:args.output.write_text(text,encoding='utf-8')
    else:print(text,end='')

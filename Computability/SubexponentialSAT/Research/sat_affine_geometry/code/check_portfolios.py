#!/usr/bin/env python3
"""Exact finite support certificates; no floating point or upstream imports."""
from fractions import Fraction
from itertools import product,combinations
from pathlib import Path
import argparse,json,random
from portfolios import load_menus,supports,operations,affine_plans,puncture,select_plan,require


def dot(a,b):
    return sum(x*y for x,y in zip(a,b))


def certify(r,plans):
    menus=[supports(r,p) for p in plans]
    q=len(menus)
    norms=[[dot(v,v) for v in menu] for menu in menus]
    pair_indices=list(combinations(range(q),2))
    grams={(i,j):[[dot(v,w) for w in menus[j]] for v in menus[i]]
           for i,j in pair_indices}
    best=-1;total=0;count=0;maximum_count=0;witness=None
    for ix in product(*(range(len(menu)) for menu in menus)):
        value=sum(norms[j][ix[j]] for j in range(q))
        value+=2*sum(grams[i,j][ix[i]][ix[j]] for i,j in pair_indices)
        if value>best:
            best=value;witness=ix;maximum_count=1
        elif value==best:
            maximum_count+=1
        total+=value;count+=1
    return {'groups':r,'Q':best,'beta_squared':str(Fraction(2*best,25*q*q*r*r)),
            'tuple_count':count,'sum_squared_norms':total,
            'maximum_count':maximum_count,'first_maximum_tuple':witness},menus,grams


def check_r12(menus,grams):
    type_bounds={(0,0):504,(0,1):500,(0,2):400,(1,1):516,(1,2):500,(2,2):540}
    # In each block: pair, pair, merge. Three discount choices per operation.
    types=[0,0,1,0,0,1,0,0,1,2]
    for (i,j),G in grams.items():
        for a,row in enumerate(G):
            for b,value in enumerate(row):
                key=tuple(sorted((types[a//3],types[b//3])))
                require(value<=type_bounds[key],'Twelve-group type bound failed')
    expected={(0,1):(1,2,0),(0,2):(1,0,2),(0,3):(2,0,1),
              (1,2):(0,2,1),(1,3):(1,2,0),(2,3):(2,1,0)}
    for pair,p in expected.items():
        G=grams[pair]
        for x in range(3):
            for y in range(3):
                require(G[27+x][27+y]==(540 if y==p[x] else 522),
                        'Preferred permutation matrix failed')
    inconsistent=[]
    for i,j,k in combinations(range(4),3):
        if all(expected[j,k][expected[i,j][x]] != expected[i,k][x]
               for x in range(3)):
            inconsistent.append([i,j,k])
    require(inconsistent==[[0,1,2],[0,2,3],[1,2,3]],'Wrong inconsistent triangles')
    best=sum((0,1,0,2)[j]==expected[i,j][(0,1,0,2)[i]]
             for i,j in expected)
    require(best==4,'Four preferred edges not attained')
    require(816+3*864+2*(3*516+3*540)==9744,'Internal bound failed')
    require(4*864+2*(6*522+4*18)==9864,'Final bound failed')
    return {'internal_tuple_upper':9744,'final_exact_Q':9864,
            'inconsistent_triangles':inconsistent}


def run():
    results=[];rng=random.Random(76123);selector_checks=0;controls=[]
    base=affine_plans()
    for item in load_menus():
        r=item['groups'];plans=item['plans']
        if r in (7,8,9):
            require(plans==puncture(base,set(range(r,9))),'Affine data disagree')
        result,menus,grams=certify(r,plans)
        for name,key in [('Q','expected_Q'),('beta_squared','beta_squared'),
                         ('tuple_count','tuple_count')]:
            require(result[name]==item[key],'Frozen certificate failed: '+name)
        if 'sum_squared_norms' in item:
            require(result['sum_squared_norms']==item['sum_squared_norms'],
                    'Support sum failed')
        if r==9:
            require(all(dot(v,v)<=486 for menu in menus for v in menu),
                    'Affine norm bound failed')
            require(all(x<=288 for G in grams.values() for row in G for x in row),
                    'Affine cross-dot bound failed')
            result['compact_affine_certificate']={'norm_upper':486,'cross_dot_upper':288}
        if r==12:
            result['compact_twelve_certificate']=check_r12(menus,grams)
        # Power-of-two dimensions have exact integral logarithms; compare selector
        # to an independently formed additive cost, including tie cases.
        for case in range(20):
            exps={(i,j):(0 if case==0 else rng.randrange(6))
                  for i in range(r) for j in range(r) if i!=j}
            dims={e:1<<v for e,v in exps.items()}
            got=select_plan(r,dims,plans)
            edge_cost=[exps[i,j]+exps[j,i] for i,j in combinations(range(r),2)]
            costs=[max(dot(v,edge_cost) for v in menu) for menu in menus]
            want=min(range(len(plans)),key=lambda j:(costs[j],j))
            require(got['selected_plan']==want,'Exact selector disagrees')
            selector_checks+=1
        bad={(i,j):1 for i in range(r) for j in range(r) if i!=j};bad[0,1]=0
        try:select_plan(r,bad,plans)
        except ValueError:controls.append('empty allocation rejected at r='+str(r))
        else:raise ValueError('Empty list accepted')
        results.append(result)
    # A one-unit stronger alleged Q would be false, detected by actual witnesses.
    require(any(r['groups']==12 and r['Q']>9863 for r in results),
            'Corrupted Q=9863 was accepted')
    controls.append('unsupported twelve-group Q=9863 rejected')
    return {'status':'PASS','certificates':results,'selector_checks':selector_checks,
            'negative_controls':controls}


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path)
    args=ap.parse_args();text=json.dumps(run(),indent=2,sort_keys=True)+'\n'
    if args.output:args.output.write_text(text,encoding='utf-8')
    else:print(text,end='')

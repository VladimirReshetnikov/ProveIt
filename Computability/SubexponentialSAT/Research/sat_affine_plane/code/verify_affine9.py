#!/usr/bin/env python3
"""Independent exhaustive certificate for the four affine-plane plans.

No source modules are imported. Vertices are F_3^2; masks are generated
from the individual edges joining matrix row/shared/column index classes.
"""
import argparse
import itertools
import json
from fractions import Fraction
from pathlib import Path


def check(ok, message):
    if not ok:
        raise RuntimeError(message)


def geometric_plans():
    vertices = [(x, y) for x in range(3) for y in range(3)]
    functionals = [(1, 0), (0, 1), (1, 1), (1, 2)]
    return [[[3*x+y for x,y in vertices if (a*x+b*y)%3 == k]
             for k in range(3)] for a,b in functionals]


def make_masks(plan):
    n = 9
    edges = list(itertools.combinations(range(n), 2))
    matrices = []
    for line in plan:
        first, second, third = line
        matrices.append(('P', ({second}, {third}, set(range(n))-{second,third})))
        matrices.append(('L', ({first}, {second,third}, set(range(n))-set(line))))
    matrices.append(('R', tuple(map(set,plan))))
    result = []
    labels = []
    for kind, (a,b,c) in matrices:
        check(not a&b and not a&c and not b&c and a|b|c==set(range(n)), 'Bad classes')
        # Construct each pair-class directly from Cartesian products.
        domains = [{tuple(sorted((x,y))) for x in u for y in v}
                   for u,v in [(a,b),(a,c),(b,c)]]
        check(sum(map(len,domains))==len(set.union(*domains)), 'Overlapping classes')
        for discounted in range(3):
            weight = {edge:0 for edge in edges}
            for j,domain in enumerate(domains):
                for edge in domain:
                    weight[edge] = 2 if j==discounted else 5
            result.append(tuple(weight[e] for e in edges))
            labels.append(kind)
    check(len(result)==21,'Mask count wrong')
    return result,labels


def certify():
    plans = geometric_plans()
    masks_labels = [make_masks(plan) for plan in plans]
    masks = [x[0] for x in masks_labels]
    labels = [x[1] for x in masks_labels]
    # Independence of the parallel classes is also checked directly.
    for p,q in itertools.combinations(plans,2):
        check(all(len(set(a)&set(b))==1 for a in p for b in q),'Non-affine parallel classes')
    by_types={}
    hist={}
    maximum=-1; total=0; count=0; witness=None
    root_values=set()
    for choice in itertools.product(range(21),repeat=4):
        vector=tuple(sum(masks[d][choice[d]][e] for d in range(4)) for e in range(36))
        square=sum(a*a for a in vector)
        types=''.join(sorted(labels[d][choice[d]] for d in range(4)))
        if types not in by_types or square>by_types[types]['max']:
            by_types[types]={'max':square,'witness':list(choice)}
        hist[square]=hist.get(square,0)+1
        if square>maximum:
            maximum=square;witness=list(choice)
        if types=='RRRR': root_values.add(square)
        total+=square;count+=1
    norm_maxima={}
    inner_maxima={}
    for k in 'PLR':
        norm_maxima[k]=max(sum(t*t for t in row) for rows,labs in masks_labels
                           for row,lab in zip(rows,labs) if lab==k)
    for k,l in itertools.combinations_with_replacement('PLR',2):
        inner_maxima[k+l]=max(sum(x*y for x,y in zip(v,w))
            for d,e in itertools.combinations(range(4),2)
            for v,lv in zip(*masks_labels[d]) for w,lw in zip(*masks_labels[e])
            if (lv,lw) in [(k,l),(l,k)])
    check(maximum==5400, 'The sharp norm bound failed')
    check(count==194481,'The exhaustive count failed')
    check(total==622974240,'The independent checksum failed')
    check(root_values=={5400},'The affine root identity failed')
    check(Fraction(2*maximum,25*4**2*9**2)==Fraction(1,3),'Normalization failed')
    return {'status':'PASS','plans':plans,'masks_per_plan':[len(x) for x in masks],
            'tuples_checked':count,'maximum_squared_norm':maximum,'first_witness':witness,
            'sum_of_squared_norms':total,'local_coefficient_squared':'1/3',
            'all_root_squared_norms':sorted(root_values),'maximum_by_sorted_operation_types':by_types,
            'max_single_mask_norm_by_type':norm_maxima,'max_transverse_inner_product_by_types':inner_maxima,
            'sharp_tuples':hist[maximum],
            'nonroot_maximum':max(z['max'] for t,z in by_types.items() if t!='RRRR')}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=certify()
    out=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(out)
    print(out,end='')

if __name__=='__main__': main()

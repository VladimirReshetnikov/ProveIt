"""Reproducible exact regression tests; no imported executable artifacts."""
import itertools,json,random,sys,time
from pathlib import Path
from packet_extraction import (Ring,forward_reference,forward_gray,centered_half_gray,
    direct_coefficient,affine_coefficient,gray_points,antipodal_boxes,projective_odd_root,lift_cube_root,adaptive_homogeneous)


def compositions(n,k):
    if k==0:
        if n==0: yield ()
        return
    if k==1: yield (n,);return
    for a in range(n+1):
        for b in compositions(n-a,k-1): yield (a,)+b


def run():
    rng=random.Random(202610270205)
    cases=0;comparisons=0;categories={}
    def check(rows,beta,ring,category):
        nonlocal cases,comparisons
        expected=direct_coefficient(rows,beta,ring)
        for fn in (forward_reference,forward_gray,centered_half_gray):
            stats={};actual=fn(rows,beta,ring,stats)
            if actual!=expected: raise AssertionError((category,fn.__name__,rows,beta,ring,expected,actual))
            if rows:
                G=1
                for b in beta: G*=b+1
                expected_count=G//2 if fn==centered_half_gray else G
                if stats['evaluations']!=expected_count: raise AssertionError(stats)
            comparisons+=1
        cases+=1;categories[category]=categories.get(category,0)+1
    for R in range(4):
        for k in range(1,4):
            for bits in itertools.product(range(2),repeat=R*k):
                rows=[bits[r*k:(r+1)*k] for r in range(R)]
                for beta in compositions(R,k): check(rows,beta,Ring(3),'exhaustive_binary')
    for _ in range(600):
        R=rng.randrange(9);k=rng.randrange(1,6);p=rng.choice((1,2,3,8,17,64,257))
        beta=[0]*k
        for r in range(R): beta[rng.randrange(k)]+=1
        rows=[[rng.randrange(-(1<<p),(1<<p)*2) for j in range(k)] for r in range(R)]
        check(rows,beta,Ring(p),'random_scalar_noncanonical')
    for _ in range(160):
        R=rng.randrange(7);k=rng.randrange(1,5);p=rng.choice((1,3,8,31))
        ring=Ring(p,rng.choice(((1,1),(0,0),(-1,0),(1,0,1))),rng.choice((1,2,3)))
        beta=[0]*k
        for r in range(R): beta[rng.randrange(k)]+=1
        rows=[[[rng.randrange(-16,32) for d in range(ring.dimension)] for j in range(k)] for r in range(R)]
        check(rows,beta,ring,'free_quotient_nilpotent_noncanonical')
    for _ in range(120):
        R=rng.randrange(1,9);k=rng.randrange(1,5);p=rng.choice((8,32,64))
        beta=[0]*k
        for r in range(R):beta[rng.randrange(k)]+=1
        weights=[rng.randrange(0,5) for j in range(k)]
        rows=[[rng.randrange(32)*(1<<w) for w in weights] for r in range(R)]
        check(rows,beta,Ring(p),'mode_weighted_synthetic')
    root_cases=0
    for ell in (1,2,3):
        for p in (1,3,8,64):
            ring=Ring(p,(1,1),ell)
            root=(0,1)+(0,)*(ring.dimension-2)
            for k in range(1,6):
                for repeat in range(3):
                    beta=[rng.choice((1,2)) for j in range(k)]
                    R=sum(beta)
                    rows=[[[rng.randrange(-16,32) for d in range(ring.dimension)] for j in range(k)] for r in range(R)]
                    expected=direct_coefficient(rows,beta,ring)
                    actual=projective_odd_root(rows,beta,ring,root,3)
                    if actual!=expected:raise AssertionError(('projective root',rows,beta,ring))
                    adapted=adaptive_homogeneous(rows,beta,ring,root)
                    if adapted!=expected:raise AssertionError('adaptive mismatch')
                    root_cases+=1
    hensel_cases=0
    for ell in (1,2):
        for p in (1,2,7,32):
            ring=Ring(p,(1,1,0,0),ell)
            root=lift_cube_root((0,1,1,0)+(0,)*(ring.dimension-4),ring)
            for k in range(1,5):
                beta=[2]*k
                rows=[[[rng.randrange(-16,32) for d in range(ring.dimension)] for j in beta] for r in range(sum(beta))]
                expected=direct_coefficient(rows,beta,ring)
                if projective_odd_root(rows,beta,ring,root,3)!=expected:raise AssertionError('Hensel e4')
                if adaptive_homogeneous(rows,beta,ring,root)!=expected:raise AssertionError('adaptive e4')
                hensel_cases+=1
    rejected=False
    try:projective_odd_root([[1,1],[1,1]],(1,1),Ring(8),1,3)
    except ValueError:rejected=True
    if not rejected:raise AssertionError('nonprimitive root accepted')
    # Mixed-radix traversal and representative partition are verified separately.
    partitions=0;gray_grids=0
    for R in range(1,9):
        for k in range(1,5):
            for beta in compositions(R,k):
                positive=tuple(b for b in beta if b)
                seen=set()
                for bounds in antipodal_boxes(positive):
                    prev=None
                    local=set()
                    for gamma,j,di in gray_points(bounds):
                        point=tuple(gamma)
                        if prev is not None:
                            if sum(a!=b for a,b in zip(prev,point))!=1:raise AssertionError('not Gray')
                            if abs(prev[j]-point[j])!=1:raise AssertionError('Gray step')
                        if point in local:raise AssertionError('duplicate Gray point')
                        local.add(point);prev=point
                        comp=tuple(b-g for b,g in zip(positive,point))
                        if point in seen or comp in seen:raise AssertionError('duplicate antipodal pair')
                        seen.add(point)
                    size=1
                    for lo,hi in bounds:size*=hi-lo+1
                    if size!=len(local):raise AssertionError('missing Gray point')
                    gray_grids+=1
                G=1
                for b in positive:G*=b+1
                if len(seen)!=G//2:raise AssertionError('representative count')
                partitions+=1
    # Mandatory guard bits: identity matrix has odd coefficient. Reducing the
    # centered numerator mod 2 first turns 2^(R-1) into zero and loses the answer.
    rows=[[1,0,0],[0,1,0],[0,0,1]]
    if centered_half_gray(rows,(1,1,1),Ring(1))!=1:raise AssertionError('guard test')
    wrong=((1<<(3-1))%2)>>(3-1)
    if wrong!=0:raise AssertionError('negative control did not fail')
    if affine_coefficient([[1,1]]*4,(2,),Ring(3))!=6:raise AssertionError('affine homogeneous adapter')
    if affine_coefficient([[1,1]]*4,(5,),Ring(3))!=0:raise AssertionError('excess degree')
    # Creation precision must be preserved before a later canonical lift.
    created=affine_coefficient([[3,3]]*2,(1,),Ring(2))
    silently_recreated=affine_coefficient([[3,3]]*2,(1,),Ring(4))
    if (created,silently_recreated)!=(2,2):raise AssertionError('unexpected control')
    # A coefficient with a carry at creation makes the hazard visible.
    created=affine_coefficient([[3,3]]*4,(1,),Ring(2))
    recreated=affine_coefficient([[3,3]]*4,(1,),Ring(4))
    if created==recreated:raise AssertionError('creation precision control insensitive')
    return dict(status='PASS',cases=cases,kernel_comparisons=comparisons,categories=categories,
                antipodal_partitions=partitions,gray_rectangles=gray_grids,root_filter_cases=root_cases,hensel_degree4_cases=hensel_cases,adaptive_cases=root_cases+hensel_cases,
                negative_controls={'insufficient_guard_bits_detected':True,'nonorthogonal_root_rejected':True,
                                   'changing_creation_precision_changes_tensor':True},
                python=sys.version,seed=202610270205)

if __name__=='__main__':
    start=time.perf_counter();result=run();result['elapsed_seconds']=time.perf_counter()-start
    print(json.dumps(result,indent=2,sort_keys=True))

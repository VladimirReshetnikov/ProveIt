#!/usr/bin/env python3
import hashlib,json,random,sys
from itertools import product
from pathlib import Path
from prism_certificate import *
from literal_composition import halt_prism,dimension_ledger,LiteralInput

RNG=random.Random(20261003)
def require(x,msg='failed'):
    if not x:raise AssertionError(msg)
def expect_bad(fn):
    try:fn()
    except (ValueError,AssertionError):return
    raise AssertionError('expected rejection')

def run(loader_root):
    receipt=Counter();examples=[]
    for dims in ((1,1,1),(2,1,1),(1,2,3),(2,2,2),(3,3,3)):
        P=Prism((-2,3,-1),dims)
        require(list(P.edges())==[P.edge_from_index(i) for i in range(P.E)])
        require(list(P.halo())==[P.halo_from_index(i) for i in range(P.H)])
        require(len(set(x for x,p in P.halo()))==P.H)
        for p in P.points():require(P.point(P.index(p))==p)
        require(sum(P.degree_histogram().values())==P.V)
        for bg in (0,4,5):
            src=PeriodicInput((1,1,1),(bg,),((P.lower,1),));C=Compiler(P,src)
            a=C.ledger(True);closed=C.closed_ledger()
            for key in closed:
                if key in a:require(a[key]==closed[key],(key,a[key],closed[key]))
            require(dict(C.collected_records())==C.polynomial(),'local collection differs')
            pol=C.polynomial()
            for _ in range(4):
                w=[RNG.randrange(5) for _ in range(P.witnesses)]
                ev=sum(c*math.prod(w[i] for i in m) for m,c in pol.items())
                require(C.evaluate(w)==ev)
                receipt['off_zero_polynomial_checks']+=1
            receipt['ledger_geometry_cases']+=1
            examples.append({'lengths':dims,'background':bg,'ledger':a})
    for dims in ((1,1,1),(2,1,1)):
        P=Prism((0,0,0),dims)
        for heights in product(range(8),repeat=P.V):
            C=Compiler(P,PeriodicInput((1,1,1),(0,),tuple(zip(P.points(),heights))))
            w=C.certificate();require(C.evaluate(w)==0)
            for i in range(len(w)):
                mutant=list(w);mutant[i]+=1
                require(C.evaluate(mutant)>0)
                receipt['single_coordinate_mutations_rejected']+=1
            receipt['canonical_witnesses_checked']+=1
    P=Prism((0,0,0),(1,1,1))
    expect_bad(lambda:Compiler(P,PeriodicInput((1,1,1),(0,),(((0,0,0),12),))).certificate())
    expect_bad(lambda:Compiler(P,PeriodicInput((1,1,1),(5,),(((0,0,0),1),))).certificate())
    expect_bad(lambda:Compiler(P,PeriodicInput((1,1,1),(0,),(((20,0,0),1),))))
    expect_bad(lambda:PeriodicInput((1,1,1),(6,)))
    expect_bad(lambda:Prism((0,0,0),(0,1,1)))
    C=Compiler(P,PeriodicInput((1,1,1),(0,)))
    w=C.certificate();expect_bad(lambda:C.evaluate([False]+w[1:]));expect_bad(lambda:C.evaluate([-1]+w[1:]))
    receipt['negative_contract_tests']=7
    # Giant indices must yield immediately, never pool coordinate ranges.
    from itertools import islice
    giant=Prism((-10**90,0,0),(10**100,10**101,10**102))
    for iterator in (giant.points(),giant.edges(),giant.halo()):require(len(tuple(islice(iterator,3)))==3)
    receipt['giant_lazy_iterator_prefixes']=3
    # The default bound is a hypothetical (T,p), not an assertion that empty U15 halts.
    for ell,right,T,p in [('','',0,0),('101','11',12,-4),('1'*20,'',40,40)]:
        Q=halt_prism(ell,right,T,p);led=dimension_ledger(Q)
        require(Q.V<=led['quadratic_volume_constant']*(len(ell)+len(right)+T+1)**2)
        require(led['witnesses']==26*Q.V-4*Q.S)
        receipt['literal_dimension_ledger_checks']+=1
    # Sample actual literal interface near known seed roots. No giant materialization.
    src=LiteralInput('10','1',loader_root);Q=src.bound_prism(0,0);src.check_prism(Q)
    for p in src.seeds:
        require(src.height(p)==6,'seed root has wrong background')
        receipt['literal_seed_height_checks']+=1
    from itertools import islice
    stream=tuple(islice(Compiler(Q,src).records(),45))
    require(len(stream)==45 and stream[0]==((0,0),1),'literal coefficient prefix differs')
    require(all(len(m)<=3 and type(co)is int and co!=0 for m,co in stream))
    receipt['literal_coefficient_prefix_records']=len(stream)
    receipt['status']='PASS'
    out={'checks':dict(receipt),'examples':examples,'scope':'New code only; no full literal prism or universal background materialized. Tests are finite evidence, not the unbounded proof.'}
    print(json.dumps(out,indent=2))
    return out

if __name__=='__main__':
    import argparse
    from literal_composition import DEFAULT_LOADER
    parser=argparse.ArgumentParser();parser.add_argument('--loader-root',type=Path,default=DEFAULT_LOADER);args=parser.parse_args()
    run(args.loader_root)

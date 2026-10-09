"""Exhaustive smoothing checks of certified prefixes; seeded order experiments."""
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent / "tests"))
from disk_oracles import *
from test_disk_scan import EagerDiskScan
ROOT = Path(sys.argv[1])
(ROOT / "results").mkdir(parents=True, exist_ok=True)
from fastunknot.disk_frontier import *
from fastunknot.radical_transfer import *
from dataclasses import asdict
from time import perf_counter_ns
import random,json


def partial_matching(pd,mask):
    components,_=circles(pd,mask)
    counts=defaultdict(int)
    for c in pd:
        for label in c:counts[label]+=1
    frontier={x for x,n in counts.items() if n==1}
    pairs=[]
    for component in components:
        ends=sorted(component&frontier)
        if len(ends)==2:pairs.append(tuple(ends))
        elif ends:raise ArithmeticError('resolution is not a one-manifold')
    return tuple(sorted(pairs))


def run():
    rng=random.Random(6170);accepted=[];declined=0;smoothing_checks=0
    for sample in range(80):
        s=rng.choice((2,3,4));n=rng.randint(max(3,s-1),8)
        word=list(range(1,s))+[rng.choice((-1,1))*rng.randint(1,s-1) for _ in range(n-s+1)]
        rng.shuffle(word);pd=braid_pd(s,word)
        start=perf_counter_ns()
        try:order=bipolar_order(pd)
        except GeometryError:declined+=1;continue
        order_ns=perf_counter_ns()-start
        prefix=[];width=0;certs=[]
        for j in order:
            prefix.append(pd[j]);cert=certify_disk(prefix)
            width=max(width,len(cert.cyclic_order));certs.append(cert.as_dict())
            for mask in range(1<<len(prefix)):
                verify_common_order([partial_matching(prefix,mask)],cert.cyclic_order)
                smoothing_checks+=1
        scan=scan_pd(pd,EagerDiskScan,order=order)
        expected=cube_ranks(pd)
        assert scan.ranks_by_degree()==expected
        assert scan.stats['disk_declines']==0
        accepted.append(dict(sample=sample,strands=s,word=word,order=order,width=width,
                             order_ns=order_ns,ranks=expected,prefix_certificates=certs))
    result=dict(seed=6170,candidates=80,accepted=len(accepted),declined=declined,
                smoothing_checks=smoothing_checks,cube_comparisons=len(accepted),cases=accepted)
    (ROOT/'results'/'geometry_validation.json').write_text(json.dumps(result,indent=2)+'\n')
    print({k:v for k,v in result.items() if k!='cases'})
    # Algebraic chain certificates, bound to the actual processed PD and disk order.
    certificates=[]
    for name,pd in [('figure-eight',braid_pd(3,[1,-2]*2)),
                    ('long-trefoil',open_edge(braid_pd(2,[1]*3))[0])]:
        scan=FastScan(shape_cache=False);prefix=[];stages=[]
        for cross in pd:
            prefix.append(cross);scan.add_crossing(cross,reduce_now=False)
            cert=certify_disk(prefix);c=snapshot(scan)
            red=reduce_complex(c,scan.algebra,cyclic_order=cert.cyclic_order,certificate=True)
            checks=verify_reduction(c,red,scan.algebra)
            stages.append(dict(prefix=[list(x) for x in prefix],disk_certificate=cert.as_dict(),
                       matchings=scan.algebra.pairs.copy(),original=asdict(c),reduced=asdict(red.complex),
                       scalar_contraction=asdict(red.contraction),inclusion=red.inclusion,
                       projection=red.projection,homotopy=red.homotopy,checks=checks,stats=red.stats))
            scan.eliminate()
        certificates.append(dict(name=name,pd=pd,stages=stages))
    (ROOT/'results'/'chain_certificates.json').write_text(json.dumps(
        dict(schema_version=1,convention='F2 Planar coefficient bits; raw homological degrees',cases=certificates),indent=2)+'\n')
    print('chain certificates:',sum(len(c['stages']) for c in certificates))
    print('long trefoil last:',certificates[-1]['stages'][-1]['original'],
          certificates[-1]['stages'][-1]['reduced'])

if __name__=='__main__':
    run()
    from disk_grid import descending_grid, verify_descending
    from fastunknot import Diagram, recognize
    grid = []
    for m in range(1,9):
        pd = descending_grid(m)
        visits = verify_descending(pd)
        d = Diagram.from_pd(pd)
        result = recognize(d, reduction="disk-adaptive")
        assert result.status == "UNKNOT"
        ranks = cube_ranks(pd) if m <= 3 else None
        if ranks is not None:
            assert sum(ranks.values()) == 2
        grid.append(dict(m=m,crossings=d.crossings,visits=len(visits),
                         ranks=ranks,method=result.method))
    (ROOT/'results'/'descending_grid.json').write_text(json.dumps(grid,indent=2)+'\n')
    print("descending grid:",grid)


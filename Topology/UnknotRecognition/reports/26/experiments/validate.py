"""Seeded, reproducible validation; writes a JSON ledger of every case."""
import json
import random
import time
from pathlib import Path
from detshadow.diagram import from_braid, Diagram
from detshadow.cube import reduced_homology
from detshadow.linalg import signed_laplacian, TerminalKernel, quotient_cofactor, bareiss, verify_kernel

ROOT=Path(__file__).resolve().parents[1]
CONWAY=((4,2,5,1),(8,4,9,3),(12,5,13,6),(2,8,3,7),(9,17,10,16),(11,18,12,19),
        (6,13,7,14),(15,20,16,21),(17,1,18,22),(19,14,20,15),(21,10,22,11))


def main():
    started=time.perf_counter(); rng=random.Random(20261007)
    diagrams=[]; homologies=[]; state_total=0
    for case in range(700):
        strands=rng.randrange(2,7); n=rng.randrange(0,11)
        word=[rng.choice((-1,1))*rng.randrange(1,strands) for _ in range(n)]
        d=from_braid(strands,word); poly=d.cube_polynomial()
        expected=tuple(sum(v for q,v in poly.items() if q%4==r) for r in range(4))
        assert d.shadow_four()==expected
        state_total += 1<<n
        diagrams.append(dict(strands=strands,word=word,shadow=list(expected)))
        if case<100 and n<=8:
            h=reduced_homology(d)
            hp=[sum((-1)**r['h']*r['rank'] for r in h['bigraded'] if r['q']%4==j) for j in range(4)]
            assert hp==list(expected)
            assert sum(map(abs,expected))<=h['rank']
            homologies.append(dict(case=case,**h))
    conway=Diagram(CONWAY)
    cp=conway.cube_polynomial(); ch=reduced_homology(conway)
    assert ch['rank']==33 and sum(map(abs,conway.euler_i()))==1
    assert conway.shadow_four()==tuple(sum(v for q,v in cp.items() if q%4==r) for r in range(4))
    graphs=[]; queries=0; singular=0
    for case in range(160):
        n=rng.randrange(2,17); b=rng.randrange(1,min(6,n)+1)
        edges=[(i,j,rng.choice((-1,1))) for i in range(n) for j in range(i+1,n) if rng.random()<0.30]
        lap=signed_laplacian(n,edges); terminals=rng.sample(range(n),b)
        kernel=TerminalKernel.build(lap,terminals)
        assert verify_kernel(lap,kernel)
        singular+=kernel.nullity>0
        qs=[]
        for _ in range(25):
            labels=[rng.randrange(b) for _ in range(b)]
            actual=kernel.query(labels)
            assert actual==bareiss(quotient_cofactor(lap,terminals,labels))
            qs.append(dict(partition=labels,determinant=actual)); queries+=1
        graphs.append(dict(vertices=n,edges=edges,terminals=terminals,nullity=kernel.nullity,queries=qs))
    result=dict(status='passed',seed=20261007,diagram_cases=len(diagrams)+1,
                direct_cube_states=state_total+(1<<11), homology_cases=len(homologies)+1,
                d2_columns=sum(x['d2_columns'] for x in homologies)+ch['d2_columns'],
                signed_graphs=len(graphs),singular_interior_graphs=singular,quotient_comparisons=queries,
                conway=dict(pd=CONWAY,shadow=conway.shadow_four(),**ch),
                elapsed_seconds=time.perf_counter()-started,
                diagrams=diagrams,homologies=homologies,graphs=graphs)
    (ROOT/'results'/'validation.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('diagrams','homologies','graphs','conway')},indent=2))

if __name__=='__main__': main()

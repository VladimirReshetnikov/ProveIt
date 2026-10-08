#!/usr/bin/env python3
"""Reproducible algebra audits, independent static determinants and certificates."""
from pathlib import Path
import sys,json,random,time,platform,hashlib
from collections import Counter
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from terminal_updates.linear import DynamicRank,det_mod,verify_normal_form,bareiss
from terminal_updates.terminal import SignedGraph,TerminalKernel,ExactObserver,quotient_cofactor,verify_exact_certificate
from terminal_updates.batch import MergePlan

def main():
    start=time.perf_counter();rng=random.Random(241);cases=Counter();updates=0
    for p in (2,3,5,101):
        for n in range(1,9):
            for trial in range(6):
                a=[[rng.randrange(p) if trial else 0 for _ in range(n)] for _ in range(n)]
                normal=DynamicRank(a,p)
                for step in range(100):
                    u=[rng.randrange(p) for _ in range(n)];v=[rng.randrange(p) for _ in range(n)]
                    cases[normal.update(u,v)]+=1
                    a=[[(a[i][j]+u[i]*v[j])%p for j in range(n)] for i in range(n)]
                    assert normal.determinant==det_mod(a,p)
                    assert verify_normal_form(a,normal.certificate())
                    updates+=1
    rng=random.Random(882);queries=0;kernels=0;singular=0;zero_kernels=0;rank_changes=0
    for nv in range(1,11):
        for trial in range(15):
            edges=tuple((i,j,rng.choice((-2,-1,1,2))) for i in range(nv) for j in range(i+1,nv) if rng.random()<0.4)
            g=SignedGraph(nv,edges);b=rng.randrange(1,nv+1);t=tuple(rng.sample(range(nv),b))
            for p in (2,3,5,101):
                k=TerminalKernel(g,t,p);cur=k.cursor();kernels+=1;singular+=int(k.nullity>0);zero_kernels+=int(k.all_zero)
                while True:
                    actual=bareiss(quotient_cofactor(g,t,cur.labels))%p
                    assert cur.residue==actual==k.query(cur.labels)
                    if cur.normal is not None:assert verify_normal_form(k.matrix_for(cur.blocks),cur.normal.certificate())
                    queries+=1
                    if len(cur.blocks)==1:break
                    source=rng.choice([a for a in cur.blocks if a]);target=rng.choice([a for a in cur.blocks if a!=source])
                    oldrank=cur.normal.rank if cur.normal else 0
                    cur=cur.merged(target,source)
                    rank_changes+=int(cur.normal is not None and oldrank!=cur.normal.rank)
    # All 877 partitions of seven terminals on an eight-vertex wheel.
    from workloads import wheel
    g,t=wheel(7,True);k=TerminalKernel(g,t,101);partitions=[]
    def rgs(prefix):
        if len(prefix)==7:partitions.append(tuple(prefix));return
        for x in range(max(prefix)+2):rgs(prefix+[x])
    rgs([0]);assert len(partitions)==877
    plan=MergePlan.compile(7,partitions);values=plan.evaluate(k)
    for labels,value in zip(partitions,values):assert value==bareiss(quotient_cofactor(g,t,labels))%101
    # Nonminimum anchor, prime-specific interior rank, and root contraction.
    g=SignedGraph(6,tuple((i,(i+1)%6,1) for i in range(6)))
    observer=ExactObserver(g,(0,1,2));cur=observer.cursor();cert_info=[]
    for name,state in [('cycle6-singleton',cur),('cycle6-nonminimum-anchor',cur.merged(2,1)),('cycle6-root-merge',cur.merged(2,1).merged(0,2))]:
        cert=state.certificate();assert verify_exact_certificate(cert)
        path=ROOT/'certificates'/f'{name}.json';path.write_text(json.dumps(cert,indent=2)+'\n')
        cert_info.append(dict(file=str(path.relative_to(ROOT)),value=state.value))
    result=dict(schema='terminal-update-audit-v1',matrix_updates=updates,matrix_cases=dict(cases),
                graph_kernels=kernels,singular_interior_kernels=singular,all_zero_kernels=zero_kernels,
                graph_queries=queries,observed_endpoint_rank_changes=rank_changes,
                exhaustive_partitions=len(partitions),compiled_merge_edges=len(plan.events),
                certificates=cert_info,elapsed_seconds=time.perf_counter()-start,
                python=sys.version,platform=platform.platform(),seeds=[241,882],
                source_sha256={str(f.relative_to(ROOT)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(list((ROOT/'terminal_updates').glob('*.py'))+[Path(__file__).resolve(),ROOT/'scripts/workloads.py'])})
    (ROOT/'results/audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()

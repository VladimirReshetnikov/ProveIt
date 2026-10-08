"""Replay the immutable dynamic-terminal delivery on native scanner queries."""
from collections import Counter
from hashlib import sha256
from io import BytesIO
import json
import random
from pathlib import Path, PurePosixPath
import subprocess
import sys
from tempfile import TemporaryDirectory
import zipfile

ROOT=Path(__file__).resolve().parents[2]
REPO=ROOT.parents[1]
ARRIVAL='49a8af358'
ARCHIVE='docs/incoming/unknot_dynamic_terminal_20261008.zip'
DIGEST='2fda8a8f8f4475256a4093796616dc0265f1029927e2e531c5c646383e68555b'


def delivery():
    blob=subprocess.check_output(['git','show',ARRIVAL+':'+ARCHIVE],cwd=REPO)
    assert sha256(blob).hexdigest()==DIGEST
    owner=TemporaryDirectory(prefix='dynamic-terminal-audit-')
    with zipfile.ZipFile(BytesIO(blob)) as z:
        for i in z.infolist():
            n=PurePosixPath(i.filename)
            assert not n.is_absolute() and '..' not in n.parts
            assert i.external_attr>>16 & 0o170000 != 0o120000
        z.extractall(owner.name)
    path=Path(owner.name)/'dynamic_terminal_20261008'
    subprocess.run([sys.executable,'-B','scripts/verify_manifest.py'],cwd=path,check=True)
    sys.path[:0]=[str(path),str(ROOT/'fast/determinant_research'),str(ROOT/'fast'),str(ROOT/'reports/26')]
    return owner,path


def main():
    owner,path=delivery()
    with owner:
        from boundary_tait import BoundaryTait,coloring
        from fastunknot import Diagram
        from fastunknot.scan_fast import FastScan
        from detshadow.diagram import complete_matching
        from integration.boundary_adapter import ModularBoundaryObserver
        from terminal_updates.batch import MergePlan
        from terminal_updates.terminal import verify_exact_certificate,reconstruct,SignedGraph,TerminalKernel
        from terminal_updates.terminal import quotient_cofactor
        from terminal_updates.linear import bareiss
        from terminal_plan import field_plan
        source=ROOT/'synthesis/data/determinant-terminal-geometry-audit.json'
        inputs=json.loads(source.read_text())['inputs']
        totals=Counter();records=[];stages=[];certificates=[]
        for number,row in enumerate(inputs):
            d=Diagram.from_braid(row['strands'],row['word']);order=row['order']
            palette=coloring(d.pd);scan=FastScan(shape_cache=False)
            for stage,index in enumerate(order):
                pairs=[scan.algebra.pairs[m] for m in sorted(set(scan.mid)-{None})]
                geometry=BoundaryTait(d.pd,order,stage,palette)
                observer=ModularBoundaryObserver(geometry)
                reference=[geometry.evaluate(p) for p in pairs]
                static=[observer.evaluate(p) for p in pairs]
                dynamic=observer.evaluate_many(pairs)
                assert reference==static==dynamic,(number,stage)
                connected=[]
                for p,(value,data) in zip(pairs,reference):
                    rebuilt=complete_matching([d.pd[i] for i in order[stage:]],p)
                    assert value==rebuilt.euler_i()
                    assert data['unreduced_euler']==2*rebuilt.euler_one()
                    assert data['shadow_components']==rebuilt.shadow_components()
                    assert data['zero_circles']==len(rebuilt.state_circles(0))
                    assert data['link_components']==rebuilt.orientation_data()[0]
                    if data['shadow_components']==1:connected.append(data['partition'])
                    else:totals['disconnected_queries']+=1
                plan=MergePlan.compile(len(geometry.terminals),connected)
                field_stats={}
                field_values=[field_plan(k,plan.events,plan.observations,stats=field_stats)
                              for k in observer.engine.kernels]
                pruned=[reconstruct(residues,observer.engine.primes,observer.engine.bound)
                        for residues in zip(*field_values)]
                assert pruned==[observer.engine.query(labels) for labels in connected]
                totals['pruned_field_updated_edges']+=field_stats.get('updated_edges',0)
                totals['pruned_field_zero_cones']+=field_stats.get('zero_cones',0)
                totals['unpruned_field_edges']+=len(plan.events)*sum(not k.all_zero for k in observer.engine.kernels)
                totals['queries']+=len(pairs);totals['merge_edges']+=len(plan.events)
                totals['stages']+=1;totals['prime_kernels']+=len(observer.engine.kernels)
                totals['singular_prime_interiors']+=sum(k.nullity>0 for k in observer.engine.kernels)
                totals['universal_zero_prime_kernels']+=sum(k.all_zero for k in observer.engine.kernels)
                totals['zero_cone_endpoint_fields']+=sum(k.nullity>len(set(labels))-1 and not k.all_zero
                    for k in observer.engine.kernels for labels in connected)
                details=dict(input=number,stage=stage,vertices=len(geometry.laplacian),
                    terminals=len(geometry.terminals),queries=len(pairs),connected=len(connected),
                    distinct_partitions=len(set(connected)),merges=len(plan.events),
                    primes=len(observer.engine.primes),nullities=[k.nullity for k in observer.engine.kernels])
                stages.append(details)
                # Nontrivial endpoint certificates, independently replayed from
                # supplied graph data; input geometry remains separately checked.
                if connected and len(certificates)<24 and len(set(connected[-1]))<len(geometry.terminals):
                    labels=connected[-1];cursor=observer.engine.cursor()
                    groups={}
                    for i,label in enumerate(labels):groups.setdefault(label,[]).append(i)
                    for group in groups.values():
                        for z in group[1:]:cursor=cursor.merged(group[0],z)
                    cert=cursor.certificate();assert verify_exact_certificate(cert)
                    certificates.append(dict(input=number,stage=stage,certificate=cert))
                records.append(dict(name=f'input_{number}_stage_{stage}',pd=d.pd,order=order,
                                    stage=stage,matchings=pairs))
                scan.add_crossing(d.pd[index])
            print('completed native input',number,flush=True)
        totals['diagrams']=len(inputs);totals['endpoint_certificates']=len(certificates)
        # A zero cone must not hide an invalid descendant merge. Cancellation
        # must propagate during validation even if every residue is zero.
        zero=TerminalKernel(SignedGraph(4,()),(0,1,2),2)
        assert field_plan(zero,[(0,0,1),(1,0,2)],[0,1,2])==[0,0,0]
        try:field_plan(zero,[(0,0,1),(1,0,2),(2,0,2)],[3])
        except ValueError:pass
        else:raise AssertionError('pruned invalid merge accepted')
        class Stop(Exception):pass
        def cancel():raise Stop()
        try:field_plan(zero,[],[0],check=cancel)
        except Stop:pass
        else:raise AssertionError('cancellation swallowed')
        rng=random.Random(261008115)
        for trial in range(200):
            n=rng.randrange(1,8);b=rng.randrange(1,n+1)
            graph=SignedGraph(n,tuple((i,j,rng.choice((-2,-1,1,2)))
                for i in range(n) for j in range(i+1,n) if rng.random()<0.4))
            terminals=tuple(rng.sample(range(n),b));labels=[tuple(range(b))];events=[]
            for _ in range(40 if b>1 else 0):
                eligible=[i for i,l in enumerate(labels) if len(set(l))>1]
                parent=rng.choice(eligible);live=set(labels[parent])
                source_anchor=rng.choice(sorted(live-{0}));target_anchor=rng.choice(sorted(live-{source_anchor}))
                events.append((parent,target_anchor,source_anchor))
                labels.append(tuple(target_anchor if x==source_anchor else x for x in labels[parent]))
            observations=list(range(len(labels)))+[0]
            for prime in (2,3,101):
                kernel=TerminalKernel(graph,terminals,prime)
                actual=field_plan(kernel,events,observations)
                expected=[bareiss(quotient_cofactor(graph,terminals,labels[i]))%prime for i in observations]
                assert actual==expected,(trial,prime)
                totals['random_field_plan_values']+=len(actual)
                totals['random_field_plans']+=1
        paths=[Path(__file__),source,ROOT/'fast/determinant_research/boundary_tait.py',
               ROOT/'fast/fastunknot/scan_fast.py',ROOT/'fast/fastunknot/boundary_connectivity.py',
               ROOT/'reports/26/detshadow/diagram.py',ROOT/'reports/26/detshadow/linalg.py',
               ROOT/'fast/determinant_research/terminal_plan.py']
        out=dict(archive_sha256=DIGEST,arrival=ARRIVAL,scope=__doc__,totals=dict(totals),stages=stages,
                 sources={str(p.relative_to(REPO)):sha256(p.read_bytes()).hexdigest() for p in paths})
        target=ROOT/'synthesis/data'
        (target/'dynamic-terminal-native-audit.json').write_text(json.dumps(out,indent=2)+'\n')
        (target/'dynamic-terminal-native-queries.json').write_text(json.dumps(records,separators=(',',':'))+'\n')
        (target/'dynamic-terminal-native-certificates.json').write_text(json.dumps(certificates,indent=2)+'\n')
        print(json.dumps(dict(totals),indent=2))


if __name__=='__main__':main()

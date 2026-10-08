"""Fresh native boundary-stage comparisons; these are not recognizer timings."""
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
import statistics
from time import perf_counter

from audit_dynamic_terminal import ROOT,REPO,delivery,DIGEST


def main():
    owner,archive=delivery()
    with owner:
        from boundary_tait import BoundaryTait
        from fastunknot import Diagram
        from detshadow.linalg import bareiss,quotient_cofactor
        from integration.boundary_adapter import ModularBoundaryObserver
        from terminal_updates.batch import MergePlan
        from terminal_updates.terminal import reconstruct
        from terminal_plan import field_plan

        data=ROOT/'synthesis/data'
        records=json.loads((data/'dynamic-terminal-native-queries.json').read_text())
        audit=json.loads((data/'dynamic-terminal-native-audit.json').read_text())
        stages=audit['stages']
        cases={'native_all':records}
        for name,key in [('native_widest',lambda r:r['terminals']),
                         ('native_many_queries',lambda r:r['queries']),
                         ('native_singular',lambda r:sum(r['nullities']))]:
            best=max(stages,key=key)
            cases[name]=[next(r for r in records if r['name']==f"input_{best['input']}_stage_{best['stage']}")]
        paths=[Path(__file__),data/'audit_dynamic_terminal.py',
               data/'dynamic-terminal-native-queries.json',data/'dynamic-terminal-native-audit.json',
               ROOT/'fast/determinant_research/boundary_tait.py',
               ROOT/'fast/determinant_research/terminal_plan.py',
               ROOT/'fast/fastunknot/diagram.py',ROOT/'fast/fastunknot/boundary_connectivity.py',
               ROOT/'reports/26/detshadow/diagram.py',ROOT/'reports/26/detshadow/linalg.py']
        hashes={str(p.relative_to(REPO)):sha256(p.read_bytes()).hexdigest() for p in paths}

        def run(rows,arm):
            out=[]
            for row in rows:
                d=Diagram.from_pd(row['pd'])
                g=BoundaryTait(d.pd,row['order'],row['stage'])
                pairs=row['matchings']
                if arm in ('rational','control'):
                    out.append([g.evaluate(p) for p in pairs])
                elif arm=='integer':
                    cache={};values=[]
                    for p in pairs:
                        meta=g.partition(p)
                        if meta['shadow_components']!=1:
                            values.append(((0,0),meta));continue
                        names={};labels=tuple(names.setdefault(v,len(names)) for v in meta['partition'])
                        if labels not in cache:
                            cache[labels]=bareiss(quotient_cofactor(g.laplacian,g.terminals,labels))
                        values.append(ModularBoundaryObserver.phased(cache[labels],meta))
                    out.append(values)
                else:
                    observer=ModularBoundaryObserver(g)
                    if arm=='static':out.append([observer.evaluate(p) for p in pairs])
                    elif arm=='static_cached':
                        values=[];cache={}
                        for p in pairs:
                            meta=g.partition(p)
                            if meta['shadow_components']!=1:
                                values.append(((0,0),meta));continue
                            names={};labels=tuple(names.setdefault(v,len(names)) for v in meta['partition'])
                            if labels not in cache:cache[labels]=observer.engine.query(labels)
                            values.append(observer.phased(cache[labels],meta))
                        out.append(values)
                    elif arm=='dynamic':out.append(observer.evaluate_many(pairs))
                    elif arm=='pruned':
                        metadata=[g.partition(p) for p in pairs]
                        connected=[m['partition'] for m in metadata if m['shadow_components']==1]
                        plan=MergePlan.compile(len(g.terminals),connected)
                        residues=[field_plan(k,plan.events,plan.observations) for k in observer.engine.kernels]
                        values=iter(reconstruct(v,observer.engine.primes,observer.engine.bound) for v in zip(*residues))
                        out.append([ModularBoundaryObserver.phased(next(values),m) if m['shadow_components']==1
                                    else ((0,0),m) for m in metadata])
                    else:raise AssertionError(arm)
            return out

        arms=('rational','control','integer','static','static_cached','dynamic','pruned')
        repetitions=dict(native_all=1,native_widest=40,native_many_queries=10,native_singular=50)
        rng=random.Random(261008116);samples=[];expected={}
        for round_number in range(6):
            jobs=[(name,arm) for name in cases for arm in arms];rng.shuffle(jobs)
            for name,arm in jobs:
                start=perf_counter()
                results=[run(cases[name],arm) for _ in range(repetitions[name])]
                elapsed=(perf_counter()-start)/repetitions[name]
                digests={sha256(json.dumps(result,sort_keys=True,separators=(',',':')).encode()).hexdigest()
                         for result in results}
                assert len(digests)==1
                digest=digests.pop()
                if name in expected:assert digest==expected[name],(name,arm)
                expected[name]=digest
                samples.append(dict(case=name,arm=arm,round=round_number,warmup=round_number==0,
                                    seconds=elapsed,result_sha256=digest))
            print('completed round',round_number,flush=True)
        for p in paths:assert sha256(p.read_bytes()).hexdigest()==hashes[str(p.relative_to(REPO))]
        summary={}
        for name,rows in cases.items():
            summary[name]=dict(stages=len(rows),queries=sum(len(r['matchings']) for r in rows),arms={})
            for arm in arms:
                s=[r for r in samples if r['case']==name and r['arm']==arm and not r['warmup']]
                ratios=[next(t['seconds'] for t in samples if t['case']==name and t['arm']=='rational'
                             and t['round']==r['round'])/r['seconds'] for r in s]
                summary[name]['arms'][arm]=dict(median_seconds=statistics.median(r['seconds'] for r in s),
                                               paired_rational_ratio=statistics.median(ratios))
        out=dict(scope=__doc__,archive_sha256=DIGEST,source_sha256=hashes,python=platform.python_version(),
                 seed=261008116,measured_batches=140,warmup_batches=28,repetitions=repetitions,
                 summary=summary,samples=samples,
                 cases={name:[r['name'] for r in rows] for name,rows in cases.items()},
                 timing='Fresh PD and boundary geometry, matrix preparation, query validation, plan compilation '
                        'and exact signed reconstruction included. Archive import, saved-input loading, output hashing '
                        'and independent validation excluded. Integer and rational arms cache normalized partitions; '
                        'static and dynamic modular arms preserve delivered behavior; static_cached adds the same '
                        'normalized partition cache. Pruned uses per-field zero-cone traversal and reconstructs '
                        'only requested outputs, whereas delivered dynamic reconstructs at every tree node. '
                        'All values and metadata must match. '
                        'These fixed finite research workloads have no production deadline contract.')
        (ROOT/'fast/results/dynamic_terminal_20261008.json').write_text(json.dumps(out,indent=2)+'\n')
        print(json.dumps(summary,indent=2))


if __name__=='__main__':main()

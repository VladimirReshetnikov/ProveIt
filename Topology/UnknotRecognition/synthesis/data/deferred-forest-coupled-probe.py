"""Research source adapter for report 105's exceptional dual selector.

Uses full original one-handle columns so deferred discovery eliminates the
lower choice. Positive trees undergo independent source geometric replay,
then ordinary core certification. No runtime strategy or checker is patched.
"""
from collections import Counter
import hashlib
import json
from pathlib import Path
import shutil
import sys
import tempfile
ROOT=Path(__file__).resolve().parents[2];DATA=Path(__file__).parent
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.core_handlebody import core_handlebody_certificate
from fastunknot.core_handlebody_verify import verify_core_handlebody_certificate
from fastunknot.core_three_handle_reduction import _dual_moves,reduce_core_three_handles
from fastunknot.core_three_handle_reduction_verify import replay_core_three_handles
from fastunknot.normal_parallelity_geometry import _parallelity_geometry
from fastunknot.normal_parallelity_reference import _reference_parallelity
from fastunknot.normal_surface_geometry import _prepare,_coordinates
from normal_orbit_research.seeds import sources


def stopping_packing(rows, budget):
    """Independent source-SCC discovery, followed by direct stopping-set checks."""
    columns={c for row in rows for c in row};edges=[set() for _ in rows];seeds=set()
    for c in columns:
        support=[r for r,row in enumerate(rows) if row.get(c,0)]
        if not any(rows[r][c]==1 for r in support):continue
        if len(support)>2:return None
        if len(support)==1:seeds.add(support[0])
        else:
            a,b=support
            if rows[a][c]==1:edges[b].add(a)
            if rows[b][c]==1:edges[a].add(b)
    reach=[]
    for r in range(len(rows)):
        seen={r};todo=[r]
        while todo:
            for v in edges[todo.pop()]-seen:seen.add(v);todo.append(v)
        reach.append(seen)
    unseen=set(range(len(rows)));groups=[]
    while unseen:
        r=min(unseen);group={v for v in unseen if v in reach[r] and r in reach[v]};unseen-=group
        if not group&seeds and not any(edges[v]&group for v in set(range(len(rows)))-group):groups.append(sorted(group))
    if len(groups)<=budget:return None
    used=set()
    for group in groups:
        assert group and not used.intersection(group);used.update(group)
        assert all(sum(rows[r].get(c,0) for r in group)!=1 for c in columns)
    return dict(schema='raw-stopping-packing-v1',row_sets=groups,maximum_top_deletions=budget)


def main():
    delivered=ROOT/'reports/105/finite_selector'
    with tempfile.TemporaryDirectory(prefix='coupled-source-forest-') as tmp:
        shutil.copytree(delivered,Path(tmp)/'solver');sys.path.insert(0,str(Path(tmp)/'solver'))
        from exceptional_forest import solve_exceptional
        pins=sources();counts=Counter();records=[]
        bank=[c for n in ('corpus.json','three_handle_corpus.json') for c in json.loads(
            (ROOT/'fast/marked_parallelity_research'/n).read_text())['cases']]
        for c in bank:
            p=_prepare(c['triangulation'],lambda:None)
            normal=_coordinates(p,c['coordinates'],lambda:None)
            g=_parallelity_geometry(p,normal,lambda:None);core=g['core']
            assert g==_reference_parallelity(p,normal,lambda:None)
            weighted,reference=reduce_core_three_handles(g,strategy='max_weight')
            assert replay_core_three_handles(g,reference)==weighted
            rows=[dict(Counter(f['handle'] for f in h['cycle'] if f['dimension']==1)) for h in core['handles2']]
            for row in rows:
                parity=[0]*len(core['handles0'])
                for e,n in row.items():
                    for v in core['handles1'][e]['ends']:parity[v]^=n%2
                assert not any(parity)
            problem=dict(vertices=len(core['handles3'])+1,columns=len(core['handles1']),
                edges=[[0 if v is None else v+1 for v in r['ends']] for r in reference['dual_endpoints']],
                rows=[sorted(row.items()) for row in rows])
            answer=solve_exceptional(problem,max_work=100000,max_partitions=500)
            counts[answer['status']]+=1
            prior=core_handlebody_certificate(weighted['core'],defer_forest=True)
            record=dict(id=c['id'],weighted_deferred_status=prior['status'],problem=problem,result=answer)
            if answer['status']=='SUCCESS':
                tree=answer['certificate']['tree'];assert len(tree)==len(set(tree))==problem['vertices']-1
                labels=list(range(problem['vertices']))
                for e in tree:
                    assert 0<=e<len(rows);a,b=(labels[v] for v in problem['edges'][e]);assert a!=b
                    labels=[min(a,b) if v in (a,b) else v for v in labels]
                assert len(set(labels))==1
                live=set(range(len(rows)))-set(tree)
                for r,e in answer['certificate']['peeling']:
                    assert r in live and rows[r].get(e)==1 and sum(rows[k].get(e,0) for k in live)==1
                    live.remove(r)
                assert not live
                ends={r['two_handle']:r['ends'] for r in reference['dual_endpoints']}
                planned=_dual_moves(ends,range(len(core['handles3'])),{e:int(e in tree) for e in ends},lambda:None)
                assert planned is not None
                moves,remaining=planned;assert {m['two_handle'] for m in moves}==set(tree)
                proof=dict(reference,cancellations=moves,surviving_two_handles=sorted(remaining))
                reduced=replay_core_three_handles(g,proof);assert reduced is not None
                result=core_handlebody_certificate(reduced['core'],defer_forest=True)
                assert result['status']=='COMPLETE' and verify_core_handlebody_certificate(reduced['core'],result['certificate'])
                record.update(top_certificate=proof,core_certificate=result['certificate'])
                counts['source_positive_replays']+=1
                if prior['status']!='COMPLETE':counts['new_bare_core_success']+=1
            if answer['status']=='NO_FOREST':
                packing=stopping_packing(rows,len(core['handles3']));assert packing is not None
                record['independent_stopping_packing']=packing;counts['independent_packing_obstructions']+=1
            records.append(record)
            if len(records)%20==0:print(len(records),dict(counts),flush=True)
        assert sources()==pins
        report=dict(native_source_sha256=pins,driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            delivered_source_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(delivered.glob('*.py'))},
            scope=__doc__,budgets=dict(max_work=100000,max_partitions=500),counts=dict(counts),cases=records)
        Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n');print(dict(counts))


if __name__=='__main__':main()

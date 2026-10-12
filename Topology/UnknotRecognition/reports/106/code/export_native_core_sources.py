"""Extract fixed-lower-forest problems from all 106 native source cuts.

No interval orbit discovery, explicit normal-disc expansion, or Regina call.
Both source-core constructors are compared exactly. This authenticates the
finite matrix extraction, not a complete native cut/handlebody conclusion.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys


def export(repo):
    fast=repo/'Topology/UnknotRecognition/fast'
    sys.path.insert(0,str(fast))
    from fastunknot.normal_surface_geometry import _prepare,_coordinates,_EDGES
    from fastunknot.normal_parallelity_geometry import _parallelity_geometry
    from fastunknot.normal_parallelity_reference import _reference_parallelity
    from fastunknot.core_handlebody import _forest,_occurrences
    from fastunknot.integer_codec import certificate_equal
    raw=(fast/'marked_parallelity_research/corpus.json').read_bytes()
    result=dict(source_pin='c6d0ec8aa0b6308310ab6c081ba29d8bc363ede5',
                corpus_sha256=hashlib.sha256(raw).hexdigest(),cases=[])
    histogram=Counter();optimal_histogram=Counter()
    check=lambda:None
    for case in json.loads(raw)['cases']:
        source=_prepare(case['triangulation'],check)
        analysed=_coordinates(source,case['coordinates'],check)
        geometry=_parallelity_geometry(source,analysed,check)
        assert certificate_equal(geometry,_reference_parallelity(source,analysed,check))
        core=geometry['core'];forest,roots=_forest(core,check)
        counts=_occurrences(core,forest,check)
        raw_counts=_occurrences(core,[],check)
        raw_owners={}
        for r,row in raw_counts.items():
            for c,a in row.items(): raw_owners.setdefault(c,[]).append((r,a))
        raw_exceptional={c for c,entries in raw_owners.items()
                         if len(entries)==3 and all(a==1 for _,a in entries)}
        preferred=sorted(core['handles1'],key=lambda h:(h['id'] not in raw_exceptional,h['id']))
        optimal_forest,_=_forest(dict(core,handles1=preferred),check)
        optimal_counts=_occurrences(core,optimal_forest,check)
        kappa=len(raw_exceptional-set(optimal_forest));optimal_histogram[kappa]+=1
        raw_column_totals=Counter()
        for h in core['handles2']:
            for flag in h['cycle']:
                if flag['dimension']==1: raw_column_totals[flag['handle']]+=1
        assert max(raw_column_totals.values(),default=0)<=3
        for h in core['handles1']:
            assert raw_column_totals[h['id']]<=(3 if h['corner']==-1 else 2)
        by_vertex={h['vertex']:h['id'] for h in core['handles3']}
        edges=[]
        for h in core['handles2']:
            t,e=divmod(h['edge'],6);a,b=_EDGES[e]
            ends=[by_vertex.get(source['vertex_roots'][4*t+v]) for v in (a,b)]
            weight=analysed['weights'][h['edge']]
            if weight:
                if h['rank']==0: ends[1]=None
                elif h['rank']==weight: ends[0]=None
                else: raise AssertionError('nonextreme source edge gap')
            else: assert h['rank']==0
            edges.append([0 if v is None else v+1 for v in ends])
        columns={}
        for r,row in counts.items():
            for c,a in row.items(): columns.setdefault(c,[]).append((r,a))
        exceptional=[c for c,entries in columns.items()
                     if len(entries)==3 and any(a==1 for _,a in entries)]
        unsupported=[c for c,entries in columns.items()
                     if len(entries)>3 and any(a==1 for _,a in entries)]
        histogram[len(exceptional)]+=1
        problem=dict(vertices=1+len(core['handles3']),columns=len(core['handles1']),edges=edges,
                     rows=[[[c,a] for c,a in sorted(counts[h['id']].items())]
                           for h in core['handles2']])
        result['cases'].append(dict(id=case['id'],tetrahedra=len(case['coordinates']),
            source_reference_equal=True,core_counts=[len(core[f'handles{i}']) for i in range(4)],
            lower_forest=forest,exceptional_columns=sorted(exceptional),
            unsupported_columns=sorted(unsupported),raw_exceptional_columns=sorted(raw_exceptional),
            maximum_raw_column_total=max(raw_column_totals.values(),default=0),
            optimal_lower_forest=optimal_forest,optimal_exceptional_count=kappa,
            optimized_problem=dict(problem,rows=[[[c,a] for c,a in sorted(optimal_counts[h['id']].items())]
                                                 for h in core['handles2']]),problem=problem))
    result['exceptional_histogram']=dict(sorted(histogram.items()))
    result['optimal_exceptional_histogram']=dict(sorted(optimal_histogram.items()))
    return result


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--repo',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    result=export(args.repo)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(cases=len(result['cases']),histogram=result['exceptional_histogram'],
                         optimal_histogram=result['optimal_exceptional_histogram'],
                         unsupported=sum(bool(c['unsupported_columns']) for c in result['cases']))))

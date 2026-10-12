"""Scope probe for report 99's polynomial two-row-column forest theorem.

This evaluates bare original core matrices, before bundle-interface rows.
It does not promote the delivered solver or claim a whole-cut census.
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
from fastunknot.core_handlebody import _forest, column_cancellation_plan
from fastunknot.core_three_handle_reduction import reduce_core_three_handles
from fastunknot.normal_parallelity_geometry import _parallelity_geometry
from fastunknot.normal_surface_geometry import _prepare,_coordinates
from normal_orbit_research.seeds import sources


def main():
    source=ROOT/'reports/99/code/forest_search'
    with tempfile.TemporaryDirectory(prefix='degree-two-source-review-') as tmp:
        shutil.copytree(source,Path(tmp)/'solver');sys.path.insert(0,str(Path(tmp)/'solver'))
        from dual_forest_search import solve_degree_two
        from dual_forest_verify import verify
        pins=sources();records=[];counts=Counter()
        bank=[c for n in ('corpus.json','three_handle_corpus.json') for c in json.loads(
            (ROOT/'fast/marked_parallelity_research'/n).read_text())['cases']]
        for c in bank:
            p=_prepare(c['triangulation'],lambda:None)
            g=_parallelity_geometry(p,_coordinates(p,c['coordinates'],lambda:None),lambda:None);core=g['core']
            tree,_=_forest(core,lambda:None);tree=set(tree)
            rows={h['id']:dict(Counter(f['handle'] for f in h['cycle'] if f['dimension']==1 and f['handle'] not in tree))
                  for h in core['handles2']}
            _,proof=reduce_core_three_handles(g,strategy='max_weight')
            problem=dict(vertices=len(core['handles3'])+1,columns=len(core['handles1']),
                         edges=[[0 if v is None else v+1 for v in r['ends']] for r in proof['dual_endpoints']],
                         rows=[sorted(row.items()) for row in rows.values()])
            result=solve_degree_two(problem)
            if result['status']!='INCONCLUSIVE':assert verify(problem,result)
            residual=column_cancellation_plan({r:rows[r] for r in proof['surviving_two_handles']})['remaining_rows']
            counts[result['status']]+=1
            if result['status']=='SUCCESS' and residual:counts['new_bare_core_completion']+=1
            columns={h:[row[h] for row in rows.values() if h in row] for h in {h for row in rows.values() for h in row}}
            unsupported=sum(1 in values and len(values)>2 for values in columns.values())
            records.append(dict(id=c['id'],three_handles=len(core['handles3']),weighted_core_complete=not residual,
                                unsupported_columns=unsupported,problem=problem,result=result))
        assert sources()==pins
        report=dict(scope=__doc__,native_source_sha256=pins,counts=dict(counts),cases=records,
                    delivered_source_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                                             for p in sorted(source.glob('*.py'))})
        Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
        print(dict(counts))
        print('Cases with three-handles:',dict(Counter(r['result']['status'] for r in records if r['three_handles'])))


if __name__=='__main__':main()

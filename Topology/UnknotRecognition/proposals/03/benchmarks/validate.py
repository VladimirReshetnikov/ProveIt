"""Validate recorded A/B results and optionally rerun the large d^2 checks.

python benchmarks/validate.py --hard --output results/validation.json
Run the unit tests separately: python -m unittest discover -s tests -v
"""
from __future__ import annotations
from collections import defaultdict
import itertools
import json
from pathlib import Path
import sys
from time import perf_counter
import argparse

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
sys.path.insert(0,str(ROOT/'tests'))
from fastunknot import Diagram,khovanov_rank
from fastunknot.algebra import Algebra
from fastunknot.simplify import simplify
from test_acceleration import noncrossing
from test_fastunknot import one_component


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--hard',action='store_true')
    parser.add_argument('--output',default='results/validation.json')
    args=parser.parse_args()
    data={'recorded_comparisons':[],'large_checks':[]}
    records=json.loads((ROOT/'results/benchmarks.json').read_text())['trials']
    groups=defaultdict(list)
    for trial in records:
        if trial['status']=='ok':groups[trial['phase'],trial['case']['name']].append(trial)
    for (phase,name),trials in groups.items():
        expected=trials[0]['result']
        for trial in trials[1:]:
            got=trial['result']
            if phase=='pipeline':assert got['status']==expected['status'],(phase,name)
            elif phase=='ordering':assert got['order']==expected['order'],(phase,name)
            else:
                assert got['rank']==expected['rank'],(phase,name)
                assert got['by_degree']==expected['by_degree'],(phase,name)
                if phase=='raw':assert got['order']==expected['order'],(phase,name)
        data['recorded_comparisons'].append({'phase':phase,'name':name,'samples':len(trials),
            'backends':sorted({x['backend'] for x in trials}),'all_agree':True})
    engine=Algebra()
    basis_entries=0
    for size in (0,2,4,6):
        matchings=list(noncrossing(list(range(size))))
        for a,b,c in itertools.product(matchings,repeat=3):
            basis_entries+=(1<<len(engine.basis(a,b).keys))*(1<<len(engine.basis(b,c).keys))
    exhaustive={n:sum(one_component(3,w) for w in itertools.product((-2,-1,1,2),repeat=n))
                for n in (2,4)}
    data['unit_test_case_counts']={'test_methods':34,'composition_basis_entries':basis_entries,
        'endomorphism_units':128,'exhaustive_three_braid_knots_by_word_length':exhaustive,
        'fresh_random_cube_diagrams':100,'pivot_policies_per_random_cube':2,
        'independent_scalar_state_sums':100,'pd_mutations':40,
        'exact_order_comparison_diagrams':50}
    if args.hard:
        d=Diagram.from_json(json.loads((ROOT/'examples/random_braid5_36.json').read_text()))
        reduced,_=simplify(d)
        ref=next(x['result'] for x in records if x['backend']=='original-markowitz')
        for diagram,label in ((d,'original36'),(reduced,'reduced24')):
            for ordering in ('greedy','natural'):
                t=perf_counter()
                order=None if ordering=='greedy' else list(range(diagram.crossings))
                result=khovanov_rank(diagram.pd,order=order,factor=False,check_d_squared=True,seconds=60)
                assert result['rank']==ref['rank']==5898
                if label=='original36':
                    assert {int(k):v for k,v in ref['by_degree'].items()}==result['by_degree']
                data['large_checks'].append({'diagram':label,'ordering':ordering,
                    'seconds':perf_counter()-t,'reduced_rank':result['reduced_rank'],
                    'd_squared_checked_each_stage':True,'result':result})
    (ROOT/args.output).write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({'all_recorded_results_agree':True,
                      'groups':len(groups),'unit_test_case_counts':data['unit_test_case_counts'],
                      'large_checks':len(data['large_checks'])},indent=2))

if __name__=='__main__':main()
